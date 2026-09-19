# -*- coding: utf-8 -*-
"""
The complete, fully automatic loop: COBOL text in, BOTH sides
generated automatically, proof out.

  - Legacy reference: cobol_extract.py (field widths) + cobol_transpile.py
    (calculation logic) -- deterministic, no LLM, no human.
  - Migrated version: convert_and_verify() from patch_loop.py -- a
    real LLM translates the COBOL on its own, and the patch loop fixes
    it over several rounds if needed.

Before this module, these two sides always ran SEPARATELY: the
transpiler was only tested against hand-written comparison functions,
never against a real LLM translation. This module is the missing
final step.
"""

import linecache

from cobol_py import CobolParserRunner, CobolParserParams, CobolSourceFormatEnum

from cobol_extract import (extract_data_items, extract_condition_names, extract_redefines_map,
                            extract_record_and_table_types, _analyze_cobol, _build_parser_params)
from cobol_transpile import transpile_procedure_division, UnsupportedCobolConstruct
from patch_loop import convert_and_verify


def expand_copy_books(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Resolves COPY statements to their actual content and returns the
    fully expanded COBOL source. Without copy_book_dirs, returns the
    source unchanged (COPY stays in the text as-is, which may lead to
    a clear error during the actual parse instead of silently being
    dropped).

    IMPORTANT: this is also needed for the LLM translation prompt --
    without resolution, the LLM would only see "COPY CUSTREC." and
    would have no knowledge of the copied fields (e.g. CUST-BALANCE),
    so it could not produce a correct translation."""
    if not copy_book_dirs:
        return cobol_source
    from cobol_py.preprocessor.preprocessor import CobolPreprocessorImpl
    params = _build_parser_params(source_format, copy_book_dirs)
    return CobolPreprocessorImpl().process(cobol_source, params)


def build_legacy_fn_from_cobol(cobol_source, function_name, param_names, return_field_py,
                                source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Builds the legacy reference function FULLY AUTOMATICALLY from COBOL --
    no human reads or transcribes the PROCEDURE DIVISION. Raises
    UnsupportedCobolConstruct with the exact error location if any part
    of the COBOL program is not covered (see cobol_transpile.py) --
    no partial translation, no silent omission.

    copy_book_dirs: optional list of directories containing COPY books
    (shared data structures, very common in real-world COBOL) --
    used both for the PROCEDURE DIVISION parse and for the
    DATA DIVISION extraction, so that both see the same, fully
    resolved fields.

    Returns (legacy_fn, generated_source, field_types_dict) -- the
    source is included so one can ALWAYS verify what was actually
    used as "ground truth", instead of trusting it blindly."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)

    items = extract_data_items(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    field_types = {it["name"]: it["field"] for it in items if it["field"]}
    field_scales = {k: v.decimal_digits for k, v in field_types.items() if hasattr(v, "decimal_digits")}
    known_cobol_names = {it["name"] for it in items}  # ALL names, including groups without their own PIC -- for the truncation safety net
    condition_name_map = extract_condition_names(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    from engine import PicX
    field_lengths = {k: v.length for k, v in field_types.items() if isinstance(v, PicX)}
    table_occurs = {it["name"]: it["table"].occurs for it in items if it["table"]}
    redefines_map = extract_redefines_map(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    record_types_for_group_check = extract_record_and_table_types(cobol_source, source_format=source_format,
                                                                    copy_book_dirs=copy_book_dirs)["record_types"]
    # Groups made up EXCLUSIVELY of PicX subfields -- enables IS NUMERIC
    # on group fields (see cobol_expr.py: group_picx_fields). Groups
    # with mixed/non-PicX subfields are deliberately excluded,
    # not guessed at.
    group_picx_fields = {
        name: list(spec.keys()) for name, spec in record_types_for_group_check.items()
        if isinstance(spec, dict) and spec and all(isinstance(v, PicX) for v in spec.values())
    }

    source = transpile_procedure_division(
        program, function_name, param_names,
        return_field_py=return_field_py, field_decimal_scales=field_scales,
        known_cobol_names=known_cobol_names, field_lengths=field_lengths,
        condition_name_map=condition_name_map, table_occurs=table_occurs,
        redefines_map=redefines_map, group_picx_fields=group_picx_fields,
    )

    namespace = {}
    filename = f"<{function_name}:auto-generated-from-cobol>"
    linecache.cache[filename] = (len(source), None, source.splitlines(keepends=True), filename)
    exec(compile(source, filename, "exec"), namespace)
    fn = namespace[function_name]
    fn.field_types = {p: field_types[p] for p in param_names if p in field_types}
    fn.field_types["return"] = field_types[return_field_py]
    table_types_dict = {it["name"]: it["table"] for it in items if it["table"]}
    fn.table_types = {p: table_types_dict[p] for p in param_names if p in table_types_dict}
    return fn, source, field_types


def full_auto_pipeline(cobol_source, function_name, param_names, return_field_py,
                        llm_fix_fn, arg_type, max_attempts=5, sandbox_timeout_seconds=None,
                        source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None, **verify_kwargs):
    """The complete loop in a single function:
      1. COBOL -> legacy reference (automatic, deterministic, see
         build_legacy_fn_from_cobol)
      2. COBOL -> initial Python translation (a real LLM, no human)
      3. verify() -> on FLAGGED: counterexample -> LLM fixes it -> re-check,
         until PROVEN or max_attempts is exhausted (see run_patch_loop)

    copy_book_dirs: see build_legacy_fn_from_cobol() -- also used to
    fully resolve the COBOL text BEFORE the LLM translation prompt
    (expand_copy_books), so that the LLM sees the same fields as the
    automatically built reference, not just a bare "COPY X.".

    Returns: PatchLoopResult (see patch_loop.py), plus a
    .legacy_source attribute (the automatically generated reference
    source, for transparency -- no one has to trust the process blindly)."""
    legacy_fn, legacy_source, field_types = build_legacy_fn_from_cobol(
        cobol_source, function_name, param_names, return_field_py,
        source_format=source_format, copy_book_dirs=copy_book_dirs,
    )
    expanded_source = expand_copy_books(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)

    result = convert_and_verify(
        legacy_fn=legacy_fn, cobol_source=expanded_source, function_name=function_name,
        param_names=param_names, llm_fix_fn=llm_fix_fn, arg_type=arg_type,
        field_types={"return": field_types[return_field_py]},
        max_attempts=max_attempts, sandbox_timeout_seconds=sandbox_timeout_seconds,
        **verify_kwargs,
    )
    result.legacy_source = legacy_source
    return result


class UnifiedVerificationResult:
    """Unified result, regardless of which of the two verification
    paths actually applied (see verify_cobol_against_modern). '.label'
    is ALWAYS 'PROVEN' or 'FLAGGED FOR MANUAL REVIEW' (or
    'VERIFIED-BY-TESTING' on the standard path) -- the caller does not
    need to know which path produced the result if only the result itself matters."""
    def __init__(self, label, path, counterexample=None, pattern=None, legacy_source=None):
        self.label = label
        self.path = path  # 'standard' or 'loop_induction'
        self.counterexample = counterexample
        self.pattern = pattern  # only set when path == 'loop_induction'
        self.legacy_source = legacy_source

    def __repr__(self):
        return (f"UnifiedVerificationResult(label={self.label!r}, path={self.path!r}, "
                f"pattern={self.pattern!r}, counterexample={self.counterexample!r})")


def verify_cobol_against_modern(cobol_source, function_name, param_names, return_field_py, modern_fn,
                                 arg_type=None, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Unified entry point: FIRST tries the normal path (automatic
    reference function from COBOL + engine.verify()) -- that covers
    the large majority of cases (constant loop bounds, everything
    else cobol_transpile.py supports).

    ONLY when automatic reference generation fails SPECIFICALLY due to
    a variable (data-dependent) PERFORM VARYING bound does it
    automatically fall back to loop_induction.py (one of the four
    accumulator patterns supported there) -- the caller does NOT need
    to know or decide which of the two verification paths is the
    right one for a given COBOL program.

    Any OTHER reason the standard path fails (unsupported statement,
    file I/O, etc.) is NOT silently caught -- only the one specific
    situation loop_induction.py actually has an answer for. Returns a
    UnifiedVerificationResult."""
    import z3
    from engine import verify as engine_verify
    from loop_induction import verify_variable_bound_loop, UnsupportedLoopPattern

    if arg_type is None:
        arg_type = z3.IntSort()

    try:
        legacy_fn, legacy_source, field_types = build_legacy_fn_from_cobol(
            cobol_source, function_name, param_names, return_field_py,
            source_format=source_format, copy_book_dirs=copy_book_dirs,
        )
    except UnsupportedCobolConstruct as e:
        if "PERFORM VARYING" in str(e) and "non-data-dependent bounds" in str(e):
            # Exactly the one known reason -- fall back to loop_induction.
            try:
                result = verify_variable_bound_loop(
                    cobol_source, modern_fn, source_format=source_format, copy_book_dirs=copy_book_dirs)
            except UnsupportedLoopPattern as e2:
                raise UnsupportedCobolConstruct(
                    f"Neither the standard path nor loop_induction.py could "
                    f"process this loop. Standard path: {e}\nloop_induction.py: {e2}"
                ) from e2
            return UnifiedVerificationResult(
                label=result["label"], path="loop_induction",
                counterexample={"k": result["counterexample_k"]} if result["counterexample_k"] is not None else None,
                pattern=result["pattern"],
            )
        raise  # any other rejection reason is NOT silently caught

    res = engine_verify(legacy_fn, modern_fn, arg_type=arg_type)
    return UnifiedVerificationResult(
        label=res.label.value, path="standard",
        counterexample=res.counterexample, legacy_source=legacy_source,
    )
