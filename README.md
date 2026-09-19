# VeriCode

**VeriCode** is a research prototype for *formally proving* behavioral
equivalence between legacy source code (COBOL, C) and its translation into a
modern language (Python, Java, C#, Go, Rust) — instead of only testing it.

Modern LLM-based code migration tools are good at producing a plausible
translation. What they generally do **not** provide is a proof that the
translation behaves identically to the original for every possible input.
VeriCode targets exactly that gap: it symbolically executes both the legacy
and the migrated code with the [Z3 SMT solver](https://github.com/Z3Prover/z3)
and tries to either prove equivalence, or produce a concrete counterexample
input on which the two programs disagree.

This is **not** a production tool. It is a working prototype built to
establish technical feasibility on a deliberately narrow slice of real-world
COBOL and C constructs. See [Limitations](#limitations) below before relying
on it for anything.

## How it works

For a given pair of functions (legacy, migrated), `engine.py` returns one of
three outcomes:

| Outcome | Meaning |
|---|---|
| `PROVEN` | Z3 proved the two functions equivalent for **all** inputs (the negation of the equivalence claim is UNSAT). |
| `VERIFIED-BY-TESTING` | The code contains constructs that cannot be proven symbolically (unbounded loops, external calls, etc.), so VeriCode falls back to differential fuzzing / concolic execution against concrete values instead. |
| `FLAGGED FOR MANUAL REVIEW` | A concrete counterexample input was found where the two functions disagree — the translation is (as far as we can tell) actually wrong on that input. |

### Pipeline

```
legacy source (COBOL / C)  ──┐
                              ├─→  transpiled into a shared, restricted
migrated source (Python /    │    Python subset that engine.py can
Java / C# / Go / Rust) ──────┘    symbolically evaluate
                                        │
                                        ▼
                        engine.py: AST → Z3 constraints
                                        │
                                        ▼
                     PROVEN / VERIFIED-BY-TESTING / FLAGGED
```

- **`engine.py`** is the core symbolic evaluator. It is deliberately
  *source-language-agnostic*: it only ever sees the shared, restricted Python
  subset. It has no idea whether that code originated from COBOL, C, Java,
  C#, Go, or Rust.
- **Language frontends** (`cobol_transpile.py` + `cobol_extract.py` for
  COBOL, `java_bridge.py`, `csharp_bridge.py`, `go_bridge.py`,
  `rust_bridge.py`, and a proof-of-concept `c_bridge.py`) each translate one
  source language into that shared Python subset via
  [`tree-sitter`](https://tree-sitter.github.io/tree-sitter/) or a dedicated
  parser (`cobol-py` for COBOL, `javalang` for Java). None of these
  frontends touch `engine.py`.
- **`loop_induction.py`** extends the symbolic path to loops whose bound is
  a *runtime value* (not a compile-time constant) for a set of common
  accumulator patterns, using mathematical induction (base case + inductive
  step) instead of unrolling.
- **`patch_loop.py`** + `llm_adapter.py` close an optional automated
  feedback loop: when Z3 finds a counterexample, it can be fed back to an
  LLM as a repair prompt, and the cycle repeats until a proof succeeds or a
  round limit is hit. This requires your own `ANTHROPIC_API_KEY`; without
  one, the loop still works with a manually supplied fix function.
- **`sandbox.py`** provides basic process isolation (not a real security
  boundary — see its docstring) for executing LLM-generated code during the
  patch loop.
- **`concolic.py`** is a lightweight concolic (concrete + symbolic) execution
  engine used as the fallback path when a function isn't fully
  symbolically provable.

## Quick start

```bash
pip install -r requirements.txt
pytest tests/ -x -q
```

To verify a single pair of functions directly:

```python
from engine import verify
import z3

def legacy(n):
    total = 0
    for i in range(n):
        total = total + i
    return total

def migrated(n):
    return n * (n - 1) // 2

result = verify(legacy, migrated, arg_type=z3.IntSort())
print(result.label, result.counterexample)
```

To go from real COBOL source to a proof, see `full_pipeline.py` for the
fully automated version (COBOL text in, both sides generated, proof out),
or `benchmarks/perf_test.py` / `benchmarks/batch_nist_test.py` for worked
examples against synthetic and NIST COBOL85 test-suite programs.

## Repository layout

```
engine.py              Core Z3 symbolic evaluator (source-language-agnostic)
loop_induction.py       Induction-based proofs for data-dependent loop bounds
cobol_extract.py        COBOL DATA DIVISION parsing (field types, PIC clauses)
cobol_transpile.py      COBOL PROCEDURE DIVISION -> shared Python subset
cobol_expr.py           COBOL expression/condition parsing helpers
java_bridge.py          Java -> shared Python subset
csharp_bridge.py        C# -> shared Python subset
go_bridge.py            Go -> shared Python subset
rust_bridge.py          Rust -> shared Python subset
c_bridge.py             C -> shared Python subset (proof-of-concept, narrow)
full_pipeline.py        End-to-end COBOL-in / proof-out automation
patch_loop.py           Automated counterexample -> LLM-fix -> re-verify loop
llm_adapter.py          Real Anthropic API adapter for patch_loop.py
sandbox.py              Process isolation for executing generated code
concolic.py             Concolic (concrete + symbolic) execution fallback
comp3_overflow.py       COBOL COMP-3 fixed-point overflow modeling
research_loop_summarization*.py   Standalone research prototypes for
                                   loop-as-recursive-relation proofs
tests/                  ~100 pytest test files covering individual language
                         constructs, bridges, edge cases, and case studies
benchmarks/             Performance and NIST COBOL85 test-suite scripts
examples/               Sample COBOL source (CBACT04C.cbl)
docs/                   Test coverage overview, verification guarantees,
                         and performance characterization
```

## Limitations

This is a prototype, and it is important to be upfront about where it
currently stands:

- **Narrow language coverage.** Each frontend supports a deliberately small
  subset of its source language (see that file's docstring for exactly
  what). `c_bridge.py` in particular is a proof-of-concept only: no
  pointers, structs, or dynamic memory.
- **Z3 performance limitation with bitwise operators.** Comparing two
  *differing* bitwise expressions (e.g. checking whether an optimization
  changed behavior) can hang indefinitely with the current
  `Int2BV`/`BV2Int`-based encoding, even though comparing simple or
  identical bitwise expressions works instantly. A native `z3.BitVec`
  encoding was confirmed to solve the same case in well under a second in
  isolation, but has not been integrated into `engine.py` because doing so
  cleanly alongside the existing COBOL decimal-scaling logic
  (`PicField.truncate()`) needs a dedicated design pass, not a quick patch.
- **No production-grade sandboxing.** `sandbox.py` provides basic crash/hang
  isolation via a subprocess, not a security boundary against a
  deliberately malicious payload — see its docstring for specifics.
- **Small, hand-picked verification corpus.** The test suite and NIST
  COBOL85 batch runs (`docs/TEST_OVERVIEW.md`,
  `docs/PERFORMANCE_CHARACTERIZATION.md`) demonstrate the approach on a
  meaningful but limited set of real and synthetic programs — not a claim
  of general-purpose COBOL coverage.

`docs/VERIFICATION_GUARANTEES.md` states precisely what a `PROVEN` result
does and does not guarantee.

## License

AGPL-3.0. See [`LICENSE`](LICENSE). If you need different terms (e.g. for
proprietary integration), open an issue to discuss.
