# -*- coding: utf-8 -*-
"""
Path 1: Automated patch loop (LLM integration), from the original concept:
"When the SMT solver finds a semantic discrepancy, it generates a precise
counterexample. This is automatically fed back to the LLM as prompt
feedback to fix the target code, until mathematical proof of equivalence
is achieved."

IMPORTANT LIMITATION: no LLM API key is available in this environment (no
ANTHROPIC_API_KEY in the container). `llm_fix_fn` is therefore an
interchangeable callback: prompt construction, counterexample extraction,
and the termination/convergence logic ARE the real patch-loop logic - only
the actual model call is replaced here by a stand-in. A production version
swaps out only `llm_fix_fn` for a real API call that uses
REPAIR_PROMPT_TEMPLATE as the prompt.
"""

import inspect
from dataclasses import dataclass, field as dc_field

from engine import Label
from sandbox import sandboxed_verify


REPAIR_PROMPT_TEMPLATE = """You are an expert in legacy code migration (COBOL -> {target_lang}).

LEGACY code (reference, ground truth):
```python
{legacy_source}
```

MIGRATED version (demonstrably diverges):
```python
{modern_source}
```

VeriCode (the Z3 SMT solver) has proven: this version is NOT equivalent to the original.
Concrete counterexample - for these inputs, both versions produce different results:
  Input:              {counterexample_text}
  Legacy output:      {legacy_output}
  Migrated output:    {modern_output}

Fix ONLY the migrated function so that it matches the legacy behavior for
this AND all other inputs. Stick to the same restriction: pure integer
arithmetic only (+, -, *, //, %, comparisons, if/elif/else, simple
assignments, for loops over range() with a constant upper bound) - no
floating-point literals, no type conversions such as int()/float()/round(),
no other function calls.
Return only the corrected Python source code of the function, no
explanation.
"""


TRANSLATION_PROMPT_TEMPLATE = """You are an expert in legacy code migration (COBOL -> Python).

Translate the following COBOL program into a single Python function.

COBOL source code:
```cobol
{cobol_source}
```

Requirements:
- The Python function must be named exactly "{function_name}".
- The parameters must have exactly these names in this order: {param_names}
- All numeric COBOL fields are already passed as scaled integers
  (e.g. a PIC 9(5)V99 field with value 12.34 corresponds to the Python
  integer 1234 - implicit 2 decimal places). Preserve this scaling in the
  translation, do NOT convert to floating-point numbers.
- IMPORTANT TECHNICAL LIMITATION of the verification system: only pure
  integer arithmetic is formally provable. Use ONLY: +, -, *, //, %,
  comparisons, if/elif/else, simple assignments, for loops over range()
  with a constant upper bound. Do NOT use floating-point literals (not even
  "* 1.5" - write e.g. "* 3 // 2" instead), NO type conversions such as
  int()/float()/round(), and NO other function calls. Such code cannot be
  formally proven, even if it is correct in its result.{structure_note}
- Return ONLY the Python source code of the function, no explanation, no imports.
"""

RECORD_NOTE_TEMPLATE = """
- The parameter "{param}" is a COBOL group field (record). Access its
  subfields EXACTLY via dot notation using these names (no other names, no
  renaming): {subfields}. Example: "{param}.{example_field}"."""

TABLE_NOTE_TEMPLATE = """
- The parameter "{param}" is a COBOL OCCURS table with {occurs} elements.
  Access it via index, e.g. "{param}[0]" through "{param}[{last_index}]"
  (0-based, not 1-based like COBOL!)."""


def build_translation_prompt(cobol_source, function_name, param_names,
                              record_types=None, table_types=None):
    structure_note = ""
    for param, subfields in (record_types or {}).items():
        names = list(subfields.keys())
        structure_note += RECORD_NOTE_TEMPLATE.format(
            param=param, subfields=", ".join(names), example_field=names[0] if names else "field",
        )
    for param, tf in (table_types or {}).items():
        structure_note += TABLE_NOTE_TEMPLATE.format(param=param, occurs=tf.occurs, last_index=tf.occurs - 1)
    return TRANSLATION_PROMPT_TEMPLATE.format(
        cobol_source=cobol_source, function_name=function_name,
        param_names=", ".join(param_names), structure_note=structure_note,
    )


def convert_and_verify(legacy_fn, cobol_source, function_name, param_names, llm_fix_fn,
                        arg_type, field_types=None, max_attempts=5, sandbox_timeout_seconds=None,
                        record_types=None, table_types=None):
    """Full conversion workflow: the LLM translates COBOL -> Python (first
    draft), after which this draft goes through the same patch loop as a
    bugfix attempt - verify() -> repair on FLAGGED -> re-check, until
    PROVEN or max_attempts is exhausted. The translation round itself does
    NOT count as a verify() round, but as a preliminary step (round 0 in
    the history).

    record_types/table_types: see run_patch_loop() - used both to build the
    translation prompt (so the LLM knows the expected names) and applied to
    the generated code after every attempt."""
    translation_prompt = build_translation_prompt(
        cobol_source, function_name, param_names, record_types=record_types, table_types=table_types)
    first_draft = llm_fix_fn(translation_prompt, 0)
    result = run_patch_loop(
        legacy_fn=legacy_fn, initial_modern_source=first_draft, function_name=function_name,
        llm_fix_fn=llm_fix_fn, arg_type=arg_type, field_types=field_types,
        max_attempts=max_attempts, sandbox_timeout_seconds=sandbox_timeout_seconds,
        record_types=record_types, table_types=table_types,
    )
    result.repairs_used += 1  # the translation round itself was also a real LLM call -
    # not counted by run_patch_loop() because it happens BEFORE the loop
    result.history.insert(0, (0, "TRANSLATION", "Initial COBOL->Python draft from the LLM", translation_prompt))
    return result


def build_repair_prompt(legacy_source, modern_source, counterexample, legacy_output, modern_output, target_lang="Rust"):
    cx_text = ", ".join(f"{k} = {v}" for k, v in counterexample.items())
    return REPAIR_PROMPT_TEMPLATE.format(
        target_lang=target_lang, legacy_source=legacy_source, modern_source=modern_source,
        counterexample_text=cx_text, legacy_output=legacy_output, modern_output=modern_output,
    )


@dataclass
class PatchLoopResult:
    success: bool
    attempts: int  # number of verify() rounds (NOT the number of LLM repair attempts!)
    repairs_used: int = 0  # number of llm_fix_fn calls actually EXECUTED - the number relevant for cost estimation
    history: list = dc_field(default_factory=list)  # [(attempt, label, detail, prompt_or_None)]
    final_source: str = None  # GUARANTEED to be the last state actually checked by verify() - never unverified LLM output


def _get_params(fn):
    return list(inspect.signature(fn).parameters.keys())


def run_patch_loop(legacy_fn, initial_modern_source, function_name, llm_fix_fn,
                    arg_type, field_types=None, max_attempts=5,
                    sandbox_timeout_seconds=None, record_types=None, table_types=None,
                    **verify_kwargs):
    """Drives the patch loop:
      1. Compile, run and verify modern_source in an ISOLATED SUBPROCESS
         (see sandbox.py) - the LLM-generated code NEVER runs in the main
         process.
      2. field_types/record_types/table_types are re-applied on EVERY
         attempt (these are part of the specification, not something the
         LLM is meant to reinvent).
      3. PROVEN -> done. FLAGGED -> build a repair prompt, call llm_fix_fn,
         adopt the new code, go back to step 1.
      4. No counterexample available (VERIFIED-BY-TESTING) -> the loop
         cannot make a targeted repair, so it aborts.
      5. The sandbox reports an error (timeout, memory limit, crash, syntax
         error in the LLM code) -> the loop aborts, and EXACTLY this is
         recorded in the result.

    record_types/table_types: dict[paramname -> RecordSpec/TableField],
    applied UNCHANGED to modern_fn (assumes the LLM addresses record
    subfields or table parameters exactly under the expected names -
    build_translation_prompt() explicitly specifies these names).
    """
    modern_source = initial_modern_source
    history = []
    legacy_params = _get_params(legacy_fn)
    last_verified_source = modern_source  # only source code that ACTUALLY went through verify()
    repairs_used = 0
    sandbox_kwargs = {}
    if sandbox_timeout_seconds is not None:
        sandbox_kwargs["timeout_seconds"] = sandbox_timeout_seconds

    for attempt in range(1, max_attempts + 1):
        outcome = sandboxed_verify(
            legacy_fn=legacy_fn, modern_source=modern_source, function_name=function_name,
            field_types=field_types, arg_type=arg_type, legacy_params=legacy_params,
            verify_kwargs=verify_kwargs, record_types=record_types, table_types=table_types,
            **sandbox_kwargs,
        )

        if "error" in outcome:
            history.append((attempt, f"SANDBOX ERROR: {outcome['error']}", "", None))
            return PatchLoopResult(success=False, attempts=attempt, repairs_used=repairs_used,
                                    history=history, final_source=last_verified_source)

        last_verified_source = modern_source  # this state was just actually checked (in the sandbox)

        if outcome["label"] == Label.PROVEN.value:
            history.append((attempt, outcome["label"], outcome["detail"], None))
            return PatchLoopResult(success=True, attempts=attempt, repairs_used=repairs_used,
                                    history=history, final_source=modern_source)

        if outcome["label"] != Label.FLAGGED.value or not outcome["counterexample"]:
            history.append((attempt, outcome["label"], outcome["detail"], None))
            return PatchLoopResult(success=False, attempts=attempt, repairs_used=repairs_used,
                                    history=history, final_source=last_verified_source)

        prompt = build_repair_prompt(
            legacy_source=inspect.getsource(legacy_fn),
            modern_source=modern_source,
            counterexample=outcome["counterexample"],
            legacy_output=outcome["legacy_out"], modern_output=outcome["modern_out"],
        )
        history.append((attempt, outcome["label"], outcome["detail"], prompt))

        if attempt == max_attempts:
            # Final round reached: no further verify() pass is possible that
            # could still check a fix from this round -> NO further
            # llm_fix_fn call (that would be a wasted API call AND would
            # otherwise leave final_source pointing at unverified code).
            break

        try:
            modern_source = llm_fix_fn(prompt, attempt)
        except Exception as e:
            # Network error, rate limit, etc. -> the loop aborts cleanly
            # instead of crashing with an unclear traceback;
            # last_verified_source (the last CHECKED state) is preserved as
            # final_source.
            history.append((attempt, f"API ERROR: {type(e).__name__}: {e}", "", None))
            return PatchLoopResult(success=False, attempts=attempt, repairs_used=repairs_used,
                                    history=history, final_source=last_verified_source)
        repairs_used += 1

    return PatchLoopResult(success=False, attempts=max_attempts, repairs_used=repairs_used,
                            history=history, final_source=last_verified_source)
