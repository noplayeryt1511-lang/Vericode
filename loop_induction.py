# -*- coding: utf-8 -*-
"""
Induction-based verification for accumulator loops with a VARIABLE
(data-dependent) bound -- the first real pipeline integration of the
technique proven in research_loop_summarization_v2.py.

DELIBERATELY NARROWLY SCOPED to EXACTLY ONE pattern (by far the most
common real-world one: a sum/counting loop over a table whose length
comes from a field at run time, not from a COBOL constant):

    PERFORM VARYING I FROM 1 BY 1 UNTIL I > <bound-field>
        ADD <table> (I) TO <accumulator>
    END-PERFORM

compared against a Python function with the same shape:

    for i in range(bound):
        accum = accum + table[i]

Anything outside this one pattern is clearly rejected, not guessed at --
nested loops, conditional accumulation, multiple state variables,
descending counters: all NOT supported. (A general derivation from an
arbitrary loop body would need a lot more work than pattern-matching
these specific shapes -- see the module-level docstrings of the
individual `verify_*` functions below for exactly what each one covers.)

Verification method: classic induction as TWO SEPARATE, each
NON-RECURSIVE Z3 queries (base case + induction step with the induction
hypothesis as an assumption) -- NOT Z3's RecFunction plus the normal
solver, which provably already fails on the trivial control case (see
research_loop_summarization.py).
"""

import ast
import inspect
import re
import textwrap

import z3

from cobol_py import CobolParserRunner, CobolParserParams, CobolSourceFormatEnum
from cobol_extract import _build_parser_params, _gather_data_description_entries, _analyze_cobol


class UnsupportedLoopPattern(Exception):
    """The loop (COBOL or Python) does not match the only currently
    supported accumulator pattern -- deliberately NOT guessed at."""
    pass


class AccumulatorLoopSpec:
    """Extracted description of an accumulator loop, independent of the
    source language: which field supplies the bound, which field is
    accumulated, which table is read, and with what coefficient/offset
    it is accumulated per step (accum + coeff * table[i] + offset) --
    IMPORTANT: coeff/offset are derived from the ACTUALLY found
    expression, NOT assumed to be 1/0. Only this way can the induction
    proof still catch real deviations (a wrong scaling factor, an extra
    constant), instead of already swallowing them during pattern matching.

    condition: optional (operator, threshold) -- IF set, accumulation
    happens per step ONLY when table[i] <operator> threshold holds
    (conditional accumulation, e.g. 'only count positive values'). None
    means: unconditional accumulation on every step (the original
    pattern)."""
    def __init__(self, bound_name, accumulator_name, table_name, coeff=1, offset=0, condition=None):
        self.bound_name = bound_name
        self.accumulator_name = accumulator_name
        self.table_name = table_name
        self.coeff = coeff
        self.offset = offset
        self.condition = condition

    def __repr__(self):
        return (f"AccumulatorLoopSpec(bound={self.bound_name!r}, accum={self.accumulator_name!r}, "
                f"table={self.table_name!r}, coeff={self.coeff}, offset={self.offset}, "
                f"condition={self.condition})")


def _py_name(cobol_name):
    return cobol_name.lower().replace("-", "_")


class NestedAccumulatorLoopSpec:
    """Extracted description of a NESTED accumulator loop: an outer loop
    with a VARIABLE bound (needs induction), an inner loop with a FIXED
    (compile-time-constant) bound (unrolled normally, like our existing
    for-loop support). The 2D table is mapped for BOTH sides (COBOL and
    Python alike) onto the SAME flat Z3 array with index 'row *
    inner_bound + column' -- matches COBOL's OCCURS-of-OCCURS storage
    layout AND can equally be used to model Python's 'table[i][j]',
    without needing two different array models."""
    def __init__(self, outer_bound_name, inner_bound, accumulator_name, table_name, coeff=1):
        self.outer_bound_name = outer_bound_name
        self.inner_bound = inner_bound
        self.accumulator_name = accumulator_name
        self.table_name = table_name
        self.coeff = coeff

    def __repr__(self):
        return (f"NestedAccumulatorLoopSpec(outer_bound={self.outer_bound_name!r}, "
                f"inner_bound={self.inner_bound}, accum={self.accumulator_name!r}, "
                f"table={self.table_name!r}, coeff={self.coeff})")


def extract_cobol_nested_accumulator_loop(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Finds a NESTED PERFORM VARYING loop: outer with a variable bound,
    inner with a FIXED (integer literal) bound, body exactly
    'ADD <table>(I J) TO <accumulator>'. Raises UnsupportedLoopPattern
    for anything that does not match exactly."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit

    def raw(node):
        return node.ctx.start.getInputStream().getText(node.ctx.start.start, node.ctx.stop.stop)

    def find_perform_statements(paragraphs):
        found = []
        for p in paragraphs:
            for s in p.statements:
                if type(s).__name__ == "PerformStatement":
                    found.append(s)
        return found

    candidates = find_perform_statements(pu.procedure_division.root_paragraphs)
    for sec in pu.procedure_division.sections:
        candidates.extend(find_perform_statements(sec.paragraphs))

    for stmt in candidates:
        text = raw(stmt).strip()
        m = re.match(
            r"^PERFORM\s+VARYING\s+([A-Za-z][A-Za-z0-9-]*)\s+FROM\s+1\s+BY\s+1\s+UNTIL\s+"
            r"\1\s*>\s*([A-Za-z][A-Za-z0-9-]*)\s+"
            r"PERFORM\s+VARYING\s+([A-Za-z][A-Za-z0-9-]*)\s+FROM\s+1\s+BY\s+1\s+UNTIL\s+"
            r"\3\s*>\s*(\d+)\s+"
            r"ADD\s+([A-Za-z][A-Za-z0-9-]*)\s*\(\s*\1\s+\3\s*\)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"END-PERFORM\s+END-PERFORM$",
            text, re.IGNORECASE | re.DOTALL,
        )
        if not m:
            continue
        outer_var, outer_bound, inner_var, inner_bound_text, table_name, accum_name = m.groups()

        paragraph_statements = None
        for p in pu.procedure_division.root_paragraphs:
            if stmt in p.statements:
                paragraph_statements = p.statements
                break
        if paragraph_statements is None:
            for sec in pu.procedure_division.sections:
                for p in sec.paragraphs:
                    if stmt in p.statements:
                        paragraph_statements = p.statements
                        break
        stmt_idx = paragraph_statements.index(stmt)
        preceding = paragraph_statements[:stmt_idx]
        init_found = any(
            re.match(rf"^MOVE\s+0\s+TO\s+{re.escape(accum_name)}$", raw(s).strip(), re.IGNORECASE)
            for s in preceding if type(s).__name__ == "MoveStatement"
        )
        if not init_found:
            raise UnsupportedLoopPattern(
                f"Accumulator '{accum_name}' is not verifiably set to 0 before the loop "
                f"-- otherwise the base case of the induction proof would just be an assumption"
            )
        return NestedAccumulatorLoopSpec(_py_name(outer_bound), int(inner_bound_text),
                                          _py_name(accum_name), _py_name(table_name))

    raise UnsupportedLoopPattern(
        "No nested PERFORM VARYING loop found that exactly matches the supported "
        "pattern (outer bound variable, inner bound FIXED/constant, body exactly "
        "'ADD <table>(I J) TO <accumulator>')."
    )


def extract_python_nested_accumulator_loop(func):
    """Finds 'for i in range(bound): for j in range(CONSTANT): accum =
    accum + table[i][j]' in a Python function. Raises
    UnsupportedLoopPattern for anything that does not match exactly."""
    src = textwrap.dedent(inspect.getsource(func))
    tree = ast.parse(src)
    fn_def = tree.body[0]

    for stmt_idx, outer in enumerate(fn_def.body):
        if not isinstance(outer, ast.For):
            continue
        if not (isinstance(outer.iter, ast.Call) and isinstance(outer.iter.func, ast.Name) and outer.iter.func.id == "range"):
            continue
        if len(outer.iter.args) != 1 or not isinstance(outer.iter.args[0], ast.Name):
            continue
        outer_bound_name = outer.iter.args[0].id
        if not isinstance(outer.target, ast.Name) or len(outer.body) != 1 or not isinstance(outer.body[0], ast.For):
            continue
        outer_var = outer.target.id
        inner = outer.body[0]

        if not (isinstance(inner.iter, ast.Call) and isinstance(inner.iter.func, ast.Name) and inner.iter.func.id == "range"):
            continue
        if len(inner.iter.args) != 1 or not isinstance(inner.iter.args[0], ast.Constant) or not isinstance(inner.iter.args[0].value, int):
            continue
        inner_bound = inner.iter.args[0].value
        if not isinstance(inner.target, ast.Name) or len(inner.body) != 1 or not isinstance(inner.body[0], ast.Assign):
            continue
        inner_var = inner.target.id
        assign = inner.body[0]
        if len(assign.targets) != 1 or not isinstance(assign.targets[0], ast.Name):
            continue
        accum_name = assign.targets[0].id
        val = assign.value
        if not (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)):
            continue

        def _extract_nested_table_term(node, _outer_var=outer_var, _inner_var=inner_var):
            """Returns (table_name, coefficient) for 'table[i][j]'
            or 'table[i][j] * N' / 'N * table[i][j]', otherwise None."""
            if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Subscript)
                    and isinstance(node.value.value, ast.Name)
                    and isinstance(node.value.slice, ast.Name) and node.value.slice.id == _outer_var
                    and isinstance(node.slice, ast.Name) and node.slice.id == _inner_var):
                return node.value.value.id, 1
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
                left, right = node.left, node.right
                if isinstance(left, ast.Constant) and isinstance(left.value, int):
                    sub = _extract_nested_table_term(right)
                    if sub:
                        return sub[0], left.value * sub[1]
                if isinstance(right, ast.Constant) and isinstance(right.value, int):
                    sub = _extract_nested_table_term(left)
                    if sub:
                        return sub[0], right.value * sub[1]
            return None

        table_name = None
        coeff = 1
        if isinstance(val.left, ast.Name) and val.left.id == accum_name:
            term = _extract_nested_table_term(val.right)
            if term:
                table_name, coeff = term
        elif isinstance(val.right, ast.Name) and val.right.id == accum_name:
            term = _extract_nested_table_term(val.left)
            if term:
                table_name, coeff = term
        if table_name is None:
            continue

        init_found = any(
            isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
            and s.targets[0].id == accum_name and isinstance(s.value, ast.Constant) and s.value.value == 0
            for s in fn_def.body[:stmt_idx]
        )
        if not init_found:
            raise UnsupportedLoopPattern(
                f"Accumulator '{accum_name}' is not verifiably set to 0 before the loop "
                f"('{accum_name} = 0' expected) -- otherwise the base case would just be an assumption"
            )
        return NestedAccumulatorLoopSpec(outer_bound_name, inner_bound, accum_name, table_name, coeff=coeff)

    raise UnsupportedLoopPattern(
        "No 'for i in range(bound): for j in range(CONSTANT): accum = accum + table[i][j]' "
        "loop found -- anything more complex is deliberately not supported."
    )


def prove_nested_accumulator_loops_equivalent(legacy_spec, modern_spec, table_z3_sort=z3.IntSort()):
    """Induction over the OUTER loop. The inner loop (fixed bound) is
    unrolled normally for each induction step: the increment per step is
    the sum of inner_bound table elements of one row (flat index
    row*inner_bound+column), exactly as an ordinary, constant-bounded
    loop would do -- no new concept, just composition."""
    if legacy_spec.inner_bound != modern_spec.inner_bound:
        return False, None  # different inner length -- cannot be equal
    inner_bound = legacy_spec.inner_bound
    table = z3.Array("table", z3.IntSort(), table_z3_sort)
    k = z3.Int("k")
    s_legacy_k = z3.Const("s_legacy_k", table_z3_sort)
    s_modern_k = z3.Const("s_modern_k", table_z3_sort)

    def row_sum(spec, row_index):
        total = None
        for j in range(inner_bound):
            term = spec.coeff * table[row_index * inner_bound + j]
            total = term if total is None else total + term
        return total

    step_legacy = s_legacy_k + row_sum(legacy_spec, k)
    step_modern = s_modern_k + row_sum(modern_spec, k)
    solver_step = z3.Solver()
    solver_step.add(k >= 0)
    solver_step.add(s_legacy_k == s_modern_k)
    solver_step.add(step_legacy != step_modern)
    res_step = solver_step.check()
    step_ok = res_step == z3.unsat
    counterexample_k = None
    if not step_ok:
        m = solver_step.model()
        counterexample_k = m.eval(k)

    return step_ok, counterexample_k


def verify_nested_accumulator_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """High-level entry point for the nested pattern, analogous to
    verify_accumulator_loop."""
    legacy_spec = extract_cobol_nested_accumulator_loop(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    modern_spec = extract_python_nested_accumulator_loop(modern_fn)

    if legacy_spec.table_name != modern_spec.table_name:
        raise UnsupportedLoopPattern(
            f"Table name does not match: COBOL '{legacy_spec.table_name}' vs. "
            f"Python '{modern_spec.table_name}'"
        )
    if legacy_spec.outer_bound_name != modern_spec.outer_bound_name:
        raise UnsupportedLoopPattern(
            f"Bound field name does not match: COBOL '{legacy_spec.outer_bound_name}' vs. "
            f"Python '{modern_spec.outer_bound_name}'"
        )
    if legacy_spec.inner_bound != modern_spec.inner_bound:
        raise UnsupportedLoopPattern(
            f"Inner bound does not match: COBOL {legacy_spec.inner_bound} vs. "
            f"Python {modern_spec.inner_bound}"
        )

    proven, counterexample_k = prove_nested_accumulator_loops_equivalent(legacy_spec, modern_spec)
    return {
        "label": "PROVEN" if proven else "FLAGGED FOR MANUAL REVIEW",
        "legacy_spec": legacy_spec,
        "modern_spec": modern_spec,
        "counterexample_k": counterexample_k,
    }


class DualAccumulatorLoopSpec:
    """Extracted description of a loop with TWO SIMULTANEOUS state
    variables: a sum accumulation (like AccumulatorLoopSpec) AND a
    simple counter (always +1 per iteration, independent of the table
    contents) -- the most common real-world pattern for "compute sum
    AND count at the same time" (e.g. for an average)."""
    def __init__(self, bound_name, table_name, sum_accum_name, count_accum_name, sum_coeff=1):
        self.bound_name = bound_name
        self.table_name = table_name
        self.sum_accum_name = sum_accum_name
        self.count_accum_name = count_accum_name
        self.sum_coeff = sum_coeff

    def __repr__(self):
        return (f"DualAccumulatorLoopSpec(bound={self.bound_name!r}, table={self.table_name!r}, "
                f"sum_accum={self.sum_accum_name!r}, count_accum={self.count_accum_name!r}, "
                f"sum_coeff={self.sum_coeff})")


def extract_cobol_dual_accumulator_loop(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Finds a PERFORM VARYING loop with EXACTLY TWO statements in the
    body: 'ADD <table>(I) [* coeff] TO <sum-accumulator>' and
    'ADD 1 TO <counter-accumulator>' (in either order). Raises
    UnsupportedLoopPattern for anything that does not match exactly."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit

    def raw(node):
        return node.ctx.start.getInputStream().getText(node.ctx.start.start, node.ctx.stop.stop)

    def find_perform_statements(paragraphs):
        found = []
        for p in paragraphs:
            for s in p.statements:
                if type(s).__name__ == "PerformStatement":
                    found.append(s)
        return found

    candidates = find_perform_statements(pu.procedure_division.root_paragraphs)
    for sec in pu.procedure_division.sections:
        candidates.extend(find_perform_statements(sec.paragraphs))

    sum_re = re.compile(
        r"^ADD\s+([A-Za-z][A-Za-z0-9-]*)\s*\(\s*([A-Za-z][A-Za-z0-9-]*)\s*\)"
        r"(?:\s*\*\s*(\d+))?\s+TO\s+([A-Za-z][A-Za-z0-9-]*)$", re.IGNORECASE)
    count_re = re.compile(r"^ADD\s+1\s+TO\s+([A-Za-z][A-Za-z0-9-]*)$", re.IGNORECASE)

    for stmt in candidates:
        text = raw(stmt).strip()
        m = re.match(
            r"^PERFORM\s+VARYING\s+([A-Za-z][A-Za-z0-9-]*)\s+FROM\s+1\s+BY\s+1\s+UNTIL\s+"
            r"\1\s*>\s*([A-Za-z][A-Za-z0-9-]*)\s+(.+?)\s+END-PERFORM$",
            text, re.IGNORECASE | re.DOTALL,
        )
        if not m:
            continue
        index_var, bound_name, body_text = m.group(1), m.group(2), m.group(3).strip()
        parts = [p.strip() for p in re.split(r"\n", body_text) if p.strip()]
        if len(parts) != 2:
            continue

        sum_match = count_match = None
        for part in parts:
            sm = sum_re.match(part)
            if sm and sm.group(2).upper() == index_var.upper():
                sum_match = sm
                continue
            cm = count_re.match(part)
            if cm:
                count_match = cm
        if sum_match is None or count_match is None:
            continue

        table_name, coeff_text, sum_accum_name = sum_match.group(1), sum_match.group(3), sum_match.group(4)
        count_accum_name = count_match.group(1)
        coeff = int(coeff_text) if coeff_text else 1

        paragraph_statements = None
        for p in pu.procedure_division.root_paragraphs:
            if stmt in p.statements:
                paragraph_statements = p.statements
                break
        if paragraph_statements is None:
            for sec in pu.procedure_division.sections:
                for p in sec.paragraphs:
                    if stmt in p.statements:
                        paragraph_statements = p.statements
                        break
        stmt_idx = paragraph_statements.index(stmt)
        preceding = paragraph_statements[:stmt_idx]

        def _init_ok(name):
            return any(
                re.match(rf"^MOVE\s+0\s+TO\s+{re.escape(name)}$", raw(s).strip(), re.IGNORECASE)
                for s in preceding if type(s).__name__ == "MoveStatement"
            )
        if not _init_ok(sum_accum_name) or not _init_ok(count_accum_name):
            raise UnsupportedLoopPattern(
                f"Both accumulators ('{sum_accum_name}', '{count_accum_name}') must be "
                f"verifiably set to 0 before the loop -- otherwise the base case would just be an assumption"
            )
        return DualAccumulatorLoopSpec(_py_name(bound_name), _py_name(table_name),
                                        _py_name(sum_accum_name), _py_name(count_accum_name), sum_coeff=coeff)

    raise UnsupportedLoopPattern(
        "No PERFORM VARYING loop with exactly two statements ('ADD <table>(I) TO <sum>' "
        "and 'ADD 1 TO <counter>', in either order) found."
    )


def extract_python_dual_accumulator_loop(func):
    """Finds 'for i in range(bound): <sum> = <sum> + table[i]; <count>
    = <count> + 1' (either order of the two statements) in a Python
    function."""
    src = textwrap.dedent(inspect.getsource(func))
    tree = ast.parse(src)
    fn_def = tree.body[0]

    for stmt_idx, stmt in enumerate(fn_def.body):
        if not isinstance(stmt, ast.For):
            continue
        if not (isinstance(stmt.iter, ast.Call) and isinstance(stmt.iter.func, ast.Name) and stmt.iter.func.id == "range"):
            continue
        if len(stmt.iter.args) != 1 or not isinstance(stmt.iter.args[0], ast.Name):
            continue
        bound_name = stmt.iter.args[0].id
        if not isinstance(stmt.target, ast.Name) or len(stmt.body) != 2:
            continue
        loop_var = stmt.target.id

        def _extract_table_term(node, _loop_var=loop_var):
            if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name)
                    and isinstance(node.slice, ast.Name) and node.slice.id == _loop_var):
                return node.value.id, 1
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
                left, right = node.left, node.right
                if isinstance(left, ast.Constant) and isinstance(left.value, int):
                    sub = _extract_table_term(right)
                    if sub:
                        return sub[0], left.value * sub[1]
                if isinstance(right, ast.Constant) and isinstance(right.value, int):
                    sub = _extract_table_term(left)
                    if sub:
                        return sub[0], right.value * sub[1]
            return None

        sum_accum_name = count_accum_name = table_name = None
        coeff = 1
        for s in stmt.body:
            if not (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)):
                sum_accum_name = None
                break
            name = s.targets[0].id
            val = s.value
            if not (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)):
                continue
            # Counter form: 'x = x + 1'
            if (isinstance(val.left, ast.Name) and val.left.id == name
                    and isinstance(val.right, ast.Constant) and val.right.value == 1):
                count_accum_name = name
                continue
            # Sum form: 'x = x + table[i]' (possibly scaled)
            term = None
            if isinstance(val.left, ast.Name) and val.left.id == name:
                term = _extract_table_term(val.right)
            elif isinstance(val.right, ast.Name) and val.right.id == name:
                term = _extract_table_term(val.left)
            if term:
                table_name, coeff = term
                sum_accum_name = name

        if sum_accum_name is None or count_accum_name is None or table_name is None:
            continue

        def _init_ok(name):
            return any(
                isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                and s.targets[0].id == name and isinstance(s.value, ast.Constant) and s.value.value == 0
                for s in fn_def.body[:stmt_idx]
            )
        if not _init_ok(sum_accum_name) or not _init_ok(count_accum_name):
            raise UnsupportedLoopPattern(
                f"Both accumulators ('{sum_accum_name}', '{count_accum_name}') must be "
                f"verifiably set to 0 before the loop -- otherwise the base case would just be an assumption"
            )
        return DualAccumulatorLoopSpec(bound_name, table_name, sum_accum_name, count_accum_name, sum_coeff=coeff)

    raise UnsupportedLoopPattern(
        "No loop with exactly two assignments ('sum = sum + table[i]' and "
        "'count = count + 1', in either order) found."
    )


def prove_dual_accumulator_loops_equivalent(legacy_spec, modern_spec, table_z3_sort=z3.IntSort()):
    """Induction over BOTH state variables simultaneously -- one
    induction step that checks both partial states together (fails if
    EITHER of the two states deviates)."""
    table = z3.Array("table", z3.IntSort(), table_z3_sort)
    k = z3.Int("k")
    sum_legacy_k = z3.Const("sum_legacy_k", table_z3_sort)
    sum_modern_k = z3.Const("sum_modern_k", table_z3_sort)
    count_legacy_k = z3.Int("count_legacy_k")
    count_modern_k = z3.Int("count_modern_k")

    step_sum_legacy = sum_legacy_k + legacy_spec.sum_coeff * table[k]
    step_sum_modern = sum_modern_k + modern_spec.sum_coeff * table[k]
    step_count_legacy = count_legacy_k + 1
    step_count_modern = count_modern_k + 1

    solver = z3.Solver()
    solver.add(k >= 0)
    solver.add(sum_legacy_k == sum_modern_k, count_legacy_k == count_modern_k)
    solver.add(z3.Or(step_sum_legacy != step_sum_modern, step_count_legacy != step_count_modern))
    res = solver.check()
    step_ok = res == z3.unsat
    counterexample_k = None
    if not step_ok:
        m = solver.model()
        counterexample_k = m.eval(k)
    return step_ok, counterexample_k


def verify_dual_accumulator_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """High-level entry point for the two-state pattern, analogous to
    verify_accumulator_loop."""
    legacy_spec = extract_cobol_dual_accumulator_loop(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    modern_spec = extract_python_dual_accumulator_loop(modern_fn)

    if legacy_spec.table_name != modern_spec.table_name:
        raise UnsupportedLoopPattern(
            f"Table name does not match: COBOL '{legacy_spec.table_name}' vs. Python '{modern_spec.table_name}'"
        )
    if legacy_spec.bound_name != modern_spec.bound_name:
        raise UnsupportedLoopPattern(
            f"Bound field name does not match: COBOL '{legacy_spec.bound_name}' vs. Python '{modern_spec.bound_name}'"
        )

    proven, counterexample_k = prove_dual_accumulator_loops_equivalent(legacy_spec, modern_spec)
    return {
        "label": "PROVEN" if proven else "FLAGGED FOR MANUAL REVIEW",
        "legacy_spec": legacy_spec,
        "modern_spec": modern_spec,
        "counterexample_k": counterexample_k,
    }


def extract_cobol_accumulator_loop(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Finds the FIRST PERFORM VARYING loop in the program that exactly
    matches the accumulator pattern, and returns an AccumulatorLoopSpec.
    Raises UnsupportedLoopPattern if no such loop is found, or the one
    found does not match exactly."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit

    def raw(node):
        return node.ctx.start.getInputStream().getText(node.ctx.start.start, node.ctx.stop.stop)

    def find_perform_statements(paragraphs):
        found = []
        for p in paragraphs:
            for s in p.statements:
                if type(s).__name__ == "PerformStatement":
                    found.append(s)
        return found

    candidates = find_perform_statements(pu.procedure_division.root_paragraphs)
    for sec in pu.procedure_division.sections:
        candidates.extend(find_perform_statements(sec.paragraphs))

    if not candidates:
        raise UnsupportedLoopPattern("No PERFORM loop found in the program")

    for stmt in candidates:
        text = raw(stmt)
        m = re.match(
            r"^PERFORM\s+VARYING\s+([A-Za-z][A-Za-z0-9-]*)\s+FROM\s+1\s+BY\s+1\s+UNTIL\s+"
            r"\1\s*>\s*([A-Za-z][A-Za-z0-9-]*)\s+(.+?)\s+END-PERFORM$",
            text.strip(), re.IGNORECASE | re.DOTALL,
        )
        if not m:
            continue
        index_var, bound_name, body_text = m.group(1), m.group(2), m.group(3).strip()

        def _check_init_and_build(accum_name, table_name, coeff, condition):
            paragraph_statements = None
            for p in pu.procedure_division.root_paragraphs:
                if stmt in p.statements:
                    paragraph_statements = p.statements
                    break
            if paragraph_statements is None:
                for sec in pu.procedure_division.sections:
                    for p in sec.paragraphs:
                        if stmt in p.statements:
                            paragraph_statements = p.statements
                            break
            stmt_idx = paragraph_statements.index(stmt)
            preceding = paragraph_statements[:stmt_idx]
            init_found = any(
                re.match(rf"^MOVE\s+0\s+TO\s+{re.escape(accum_name)}$", raw(s).strip(), re.IGNORECASE)
                for s in preceding if type(s).__name__ == "MoveStatement"
            )
            if not init_found:
                raise UnsupportedLoopPattern(
                    f"Accumulator '{accum_name}' is not verifiably set to 0 before the loop "
                    f"('MOVE 0 TO {accum_name}' expected in the same paragraph) -- otherwise the "
                    f"base case of the induction proof would just be an assumption, not a real check"
                )
            return AccumulatorLoopSpec(_py_name(bound_name), _py_name(accum_name), _py_name(table_name),
                                        coeff=coeff, condition=condition)

        # Pattern 1: unconditional accumulation -- 'ADD <table>(I) [* coeff] TO <accumulator>'
        m_body = re.match(
            r"^ADD\s+([A-Za-z][A-Za-z0-9-]*)\s*\(\s*" + re.escape(index_var) + r"\s*\)"
            r"(?:\s*\*\s*(\d+))?\s+TO\s+([A-Za-z][A-Za-z0-9-]*)$",
            body_text, re.IGNORECASE,
        )
        if m_body:
            table_name, coeff_text, accum_name = m_body.group(1), m_body.group(2), m_body.group(3)
            coeff = int(coeff_text) if coeff_text else 1
            return _check_init_and_build(accum_name, table_name, coeff, condition=None)

        # Pattern 2: CONDITIONAL accumulation -- 'IF <table>(I) (< | <= | > | >= | =) <threshold>
        # ADD <constant> TO <accumulator> END-IF' (e.g. "only count positive values")
        m_cond = re.match(
            r"^IF\s+([A-Za-z][A-Za-z0-9-]*)\s*\(\s*" + re.escape(index_var) + r"\s*\)\s*"
            r"(<=|>=|<|>|=)\s*(-?\d+)\s+ADD\s+(\d+)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+END-IF$",
            body_text, re.IGNORECASE,
        )
        if m_cond:
            table_name, op, threshold, coeff_text, accum_name = m_cond.groups()
            coeff = int(coeff_text)
            condition = (op, int(threshold))
            return _check_init_and_build(accum_name, table_name, coeff, condition=condition)

    raise UnsupportedLoopPattern(
        "No PERFORM VARYING loop found that matches either of the two supported accumulator "
        "patterns: unconditional ('ADD <table>(I) TO <accumulator>') or conditional ('IF <table>(I) OP "
        "<threshold> ADD <constant> TO <accumulator> END-IF') -- anything more complex (multiple "
        "statements in the loop body, descending counters, multiple state variables) is deliberately not supported."
    )


def extract_python_accumulator_loop(func):
    """Finds a 'for i in range(bound): accum = accum + table[i]' pattern
    (in either order of the operands) in a Python function, and returns
    an AccumulatorLoopSpec. Raises UnsupportedLoopPattern for anything
    that does not match exactly."""
    src = textwrap.dedent(inspect.getsource(func))
    tree = ast.parse(src)
    fn_def = tree.body[0]

    for stmt_idx, stmt in enumerate(fn_def.body):
        if not isinstance(stmt, ast.For):
            continue
        if not (isinstance(stmt.iter, ast.Call) and isinstance(stmt.iter.func, ast.Name) and stmt.iter.func.id == "range"):
            continue
        if len(stmt.iter.args) != 1 or not isinstance(stmt.iter.args[0], ast.Name):
            continue  # only 'range(ONE_NAME)' is supported, not range(0,n) or similar
        bound_name = stmt.iter.args[0].id
        if not isinstance(stmt.target, ast.Name):
            continue
        loop_var = stmt.target.id

        def _extract_table_term(node):
            """Returns (table_name, coefficient) if node is 'table[i]'
            or 'table[i] * N' / 'N * table[i]', otherwise None."""
            if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name)
                    and isinstance(node.slice, ast.Name) and node.slice.id == loop_var):
                return node.value.id, 1
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
                left, right = node.left, node.right
                if isinstance(left, ast.Constant) and isinstance(left.value, int):
                    sub = _extract_table_term(right)
                    if sub:
                        return sub[0], left.value * sub[1]
                if isinstance(right, ast.Constant) and isinstance(right.value, int):
                    sub = _extract_table_term(left)
                    if sub:
                        return sub[0], right.value * sub[1]
            return None

        def _check_init_and_build(accum_name, table_name, coeff, condition):
            init_found = any(
                isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                and s.targets[0].id == accum_name and isinstance(s.value, ast.Constant) and s.value.value == 0
                for s in fn_def.body[:stmt_idx]
            )
            if not init_found:
                raise UnsupportedLoopPattern(
                    f"Accumulator '{accum_name}' is not verifiably set to 0 before the loop "
                    f"('{accum_name} = 0' expected before the for loop) -- otherwise the base "
                    f"case of the induction proof would just be an assumption, not a real check"
                )
            return AccumulatorLoopSpec(bound_name, accum_name, table_name, coeff=coeff, condition=condition)

        if len(stmt.body) == 1 and isinstance(stmt.body[0], ast.Assign):
            # Pattern 1: unconditional accumulation -- 'accum = accum + table[i]'
            # (or 'table[i] + accum', possibly with a constant scaling factor)
            assign = stmt.body[0]
            if len(assign.targets) == 1 and isinstance(assign.targets[0], ast.Name):
                accum_name = assign.targets[0].id
                val = assign.value

                def _is_accum_name(node, _accum_name=accum_name):
                    return isinstance(node, ast.Name) and node.id == _accum_name

                if isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add):
                    table_name, coeff = None, 1
                    if _is_accum_name(val.left):
                        term = _extract_table_term(val.right)
                        if term:
                            table_name, coeff = term
                    elif _is_accum_name(val.right):
                        term = _extract_table_term(val.left)
                        if term:
                            table_name, coeff = term
                    if table_name is not None:
                        return _check_init_and_build(accum_name, table_name, coeff, condition=None)

        if len(stmt.body) == 1 and isinstance(stmt.body[0], ast.If):
            # Pattern 2: CONDITIONAL accumulation -- 'if table[i] OP threshold:
            # accum = accum + constant' (no else, no elif)
            if_stmt = stmt.body[0]
            if not if_stmt.orelse and len(if_stmt.body) == 1 and isinstance(if_stmt.body[0], ast.Assign):
                cond = if_stmt.test
                inner_assign = if_stmt.body[0]
                _CMP_OPS = {ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">=", ast.Eq: "="}
                if (isinstance(cond, ast.Compare) and len(cond.ops) == 1 and len(cond.comparators) == 1
                        and type(cond.ops[0]) in _CMP_OPS):
                    term = _extract_table_term(cond.left)
                    threshold_node = cond.comparators[0]
                    if term and isinstance(threshold_node, ast.Constant) and isinstance(threshold_node.value, int):
                        table_name, table_coeff = term
                        if table_coeff == 1 and len(inner_assign.targets) == 1 and isinstance(inner_assign.targets[0], ast.Name):
                            accum_name = inner_assign.targets[0].id
                            val = inner_assign.value
                            if (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)
                                    and isinstance(val.left, ast.Name) and val.left.id == accum_name
                                    and isinstance(val.right, ast.Constant) and isinstance(val.right.value, int)):
                                coeff = val.right.value
                                condition = (_CMP_OPS[type(cond.ops[0])], threshold_node.value)
                                return _check_init_and_build(accum_name, table_name, coeff, condition=condition)

    raise UnsupportedLoopPattern(
        "No 'for i in range(bound): accum = accum + table[i]' loop (unconditional) or "
        "'for i in range(bound): if table[i] OP threshold: accum = accum + constant' loop "
        "(conditional) found in the function -- anything more complex is deliberately not supported."
    )


def prove_accumulator_loops_equivalent(legacy_spec, modern_spec, table_z3_sort=z3.IntSort()):
    """The actual proof: classic induction. The BASE CASE is already
    checked structurally during extraction (both sides must verifiably
    initialize their accumulator to 0, see
    extract_cobol_accumulator_loop/extract_python_accumulator_loop) --
    what remains here is only the INDUCTION STEP as the actual Z3
    query. IMPORTANT: uses the coefficients ACTUALLY extracted from
    both sides (legacy_spec.coeff / modern_spec.coeff) -- a wrong
    scaling factor on one side leads to a REAL deviation in the
    induction step, so it is actually caught, not already swallowed
    during pattern matching. Returns (proven: bool, counterexample_k:
    int|None)."""
    table = z3.Array("table", z3.IntSort(), table_z3_sort)
    k = z3.Int("k")
    s_legacy_k = z3.Const("s_legacy_k", table_z3_sort)
    s_modern_k = z3.Const("s_modern_k", table_z3_sort)

    _Z3_OPS = {
        "<": lambda a, b: a < b, "<=": lambda a, b: a <= b,
        ">": lambda a, b: a > b, ">=": lambda a, b: a >= b, "=": lambda a, b: a == b,
    }

    def _step_expr(spec, s_k):
        if spec.condition is None:
            # Pattern 1: unconditional accumulation -- the increment is coeff * table[k]
            term = spec.coeff * table[k]
            return s_k + term
        # Pattern 2: conditional accumulation -- the increment is the
        # CONSTANT coeff itself (e.g. "ADD 1"), NOT coeff * table[k] --
        # table[k] is needed here ONLY for the condition (guard), not as
        # a factor of the increment. An earlier, incorrect version
        # mistakenly multiplied by table[k], which caused the error to
        # cancel itself out exactly at the critical point table[k]=0
        # (times 0), swallowing the edge-case bug it was meant to find.
        op, threshold = spec.condition
        guard = _Z3_OPS[op](table[k], z3.IntVal(threshold))
        return z3.If(guard, s_k + spec.coeff, s_k)

    step_legacy = _step_expr(legacy_spec, s_legacy_k)
    step_modern = _step_expr(modern_spec, s_modern_k)
    solver_step = z3.Solver()
    solver_step.add(k >= 0)
    solver_step.add(s_legacy_k == s_modern_k)
    solver_step.add(step_legacy != step_modern)
    res_step = solver_step.check()
    step_ok = res_step == z3.unsat
    counterexample_k = None
    if not step_ok:
        m = solver_step.model()
        counterexample_k = m.eval(k)

    return step_ok, counterexample_k


def verify_accumulator_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """High-level entry point: extracts the accumulator pattern from
    COBOL AND from a Python function, checks that both access the SAME
    table/bound field name (otherwise a comparison would not be
    meaningful), and runs the induction proof. Returns a dict:
    {label: 'PROVEN'|'FLAGGED FOR MANUAL REVIEW', legacy_spec,
    modern_spec, counterexample_k}."""
    legacy_spec = extract_cobol_accumulator_loop(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    modern_spec = extract_python_accumulator_loop(modern_fn)

    if legacy_spec.table_name != modern_spec.table_name:
        raise UnsupportedLoopPattern(
            f"Table name does not match: COBOL '{legacy_spec.table_name}' vs. "
            f"Python '{modern_spec.table_name}' -- no meaningful comparison possible"
        )
    if legacy_spec.bound_name != modern_spec.bound_name:
        raise UnsupportedLoopPattern(
            f"Bound field name does not match: COBOL '{legacy_spec.bound_name}' vs. "
            f"Python '{modern_spec.bound_name}' -- no meaningful comparison possible"
        )

    proven, counterexample_k = prove_accumulator_loops_equivalent(legacy_spec, modern_spec)
    return {
        "label": "PROVEN" if proven else "FLAGGED FOR MANUAL REVIEW",
        "legacy_spec": legacy_spec,
        "modern_spec": modern_spec,
        "counterexample_k": counterexample_k,
    }


def verify_variable_bound_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Unified entry point: tries ALL FOUR supported accumulator patterns
    in turn (simple, conditional, nested, two simultaneous states) and
    uses the first one that matches on both the COBOL and the Python
    side -- the caller no longer needs to know/decide which of the four
    patterns applies.

    This removes the need to manually pick the right one of the four
    verify_* functions. IMPORTANT: this is still purely PATTERN MATCHING, not a
    general derivation from an arbitrary loop body -- a loop that
    matches NONE of the four patterns is still clearly rejected with
    UnsupportedLoopPattern, not guessed at.

    Returns a dict: {label, legacy_spec, modern_spec, counterexample_k,
    pattern} -- 'pattern' names which of the four patterns actually
    applied ('single'|'conditional'|'nested'|'dual')."""
    attempts = [
        ("single", verify_accumulator_loop),  # internally covers BOTH the simple AND the conditional pattern (see AccumulatorLoopSpec.condition)
        ("nested", verify_nested_accumulator_loop),
        ("dual", verify_dual_accumulator_loop),
    ]
    errors = []
    for name, fn in attempts:
        try:
            result = fn(cobol_source, modern_fn, source_format=source_format, copy_book_dirs=copy_book_dirs)
            result["pattern"] = name
            return result
        except UnsupportedLoopPattern as e:
            errors.append(f"  - {name}: {e}")

    raise UnsupportedLoopPattern(
        "No loop found that matches any of the four supported accumulator patterns "
        "(simple, conditional, nested, two simultaneous states). Details:\n" + "\n".join(errors)
    )


def extract_cobol_file_accumulator_loop(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """A FIFTH pattern, structurally motivated differently from the first
    four: 'PERFORM UNTIL <eof-field> = <value> / READ <file> AT END MOVE
    <value> TO <eof-field> NOT AT END ADD <record-field> TO
    <accumulator> END-READ / END-PERFORM' -- by far the most common
    real-world form of a file-processing loop.

    The key insight: 'sum a field over all records of a file of unknown
    length' is STRUCTURALLY IDENTICAL to 'sum a table element over a
    table of unknown length' -- exactly what AccumulatorLoopSpec already
    proves. The number of records is treated as an IMPLICIT, synthetic
    bound parameter (fixed name 'record_count' -- a convention the
    calling reference function on the modern side must know as an
    additional parameter), and the field read is treated as an implicit
    table (name = the Python name of the record field itself, e.g.
    'fd_amount' stands for 'the array of FD-AMOUNT values across all
    records')."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit

    def raw(node):
        return node.ctx.start.getInputStream().getText(node.ctx.start.start, node.ctx.stop.stop)

    def find_perform_statements(paragraphs):
        found = []
        for p in paragraphs:
            for s in p.statements:
                if type(s).__name__ == "PerformStatement":
                    found.append(s)
        return found

    candidates = find_perform_statements(pu.procedure_division.root_paragraphs)
    for sec in pu.procedure_division.sections:
        candidates.extend(find_perform_statements(sec.paragraphs))

    for stmt in candidates:
        text = raw(stmt).strip()
        # TWO forms are supported: unconditional accumulation
        # ('NOT AT END ADD <field> TO <accum>') AND conditional
        # accumulation ('NOT AT END IF <field> OP <threshold> ADD
        # <constant> TO <accum> END-IF') -- the latter is very common in
        # real-world code ("only count records above a threshold"). Both
        # map onto the same AccumulatorLoopSpec, the conditional one via
        # its already existing condition field (see the conditional
        # PERFORM VARYING variant).
        m = re.match(
            r"^PERFORM\s+UNTIL\s+([A-Za-z][A-Za-z0-9-]*)\s*=\s*([A-Za-z0-9][A-Za-z0-9-]*)\s+"
            r"READ\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+"
            r"AT\s+END\s+MOVE\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"NOT\s+AT\s+END\s+ADD\s+([A-Za-z][A-Za-z0-9-]*)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"END-READ\s+END-PERFORM$",
            text, re.IGNORECASE | re.DOTALL,
        )
        condition = None
        coeff = 1
        if m:
            (eof_field_1, eof_value_1, _file_name, eof_value_2, eof_field_2,
             record_field, accum_name) = m.groups()
        else:
            m_cond = re.match(
                r"^PERFORM\s+UNTIL\s+([A-Za-z][A-Za-z0-9-]*)\s*=\s*([A-Za-z0-9][A-Za-z0-9-]*)\s+"
                r"READ\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+"
                r"AT\s+END\s+MOVE\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
                r"NOT\s+AT\s+END\s+"
                r"IF\s+([A-Za-z][A-Za-z0-9-]*)\s*(>=|<=|>|<|=)\s*(-?\d+)\s+"
                r"ADD\s+(\d+)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
                r"END-IF\s+END-READ\s+END-PERFORM$",
                text, re.IGNORECASE | re.DOTALL,
            )
            if not m_cond:
                continue
            (eof_field_1, eof_value_1, _file_name, eof_value_2, eof_field_2,
             record_field, op_text, threshold_text, coeff_text, accum_name) = m_cond.groups()
            condition = (op_text, int(threshold_text))
            coeff = int(coeff_text)
        if eof_field_1.upper() != eof_field_2.upper() or eof_value_1.upper() != eof_value_2.upper():
            continue  # the same EOF flag/value must match on both sides

        paragraph_statements = None
        for p in pu.procedure_division.root_paragraphs:
            if stmt in p.statements:
                paragraph_statements = p.statements
                break
        if paragraph_statements is None:
            for sec in pu.procedure_division.sections:
                for p in sec.paragraphs:
                    if stmt in p.statements:
                        paragraph_statements = p.statements
                        break
        stmt_idx = paragraph_statements.index(stmt)
        preceding = paragraph_statements[:stmt_idx]
        init_found = any(
            re.match(rf"^MOVE\s+0\s+TO\s+{re.escape(accum_name)}$", raw(s).strip(), re.IGNORECASE)
            for s in preceding if type(s).__name__ == "MoveStatement"
        )
        if not init_found:
            raise UnsupportedLoopPattern(
                f"Accumulator '{accum_name}' is not verifiably set to 0 before the loop "
                f"-- otherwise the base case of the induction proof would just be an assumption"
            )
        return AccumulatorLoopSpec(
            bound_name="record_count",  # SYNTHETIC -- fixed convention, see the docstring above
            accumulator_name=_py_name(accum_name),
            table_name=_py_name(record_field),
            coeff=coeff, offset=0, condition=condition,
        )

    raise UnsupportedLoopPattern(
        "No file-processing loop found that exactly matches the supported pattern "
        "('PERFORM UNTIL <eof> = <value> / READ <file> AT END MOVE <value> TO <eof> "
        "NOT AT END ADD <field> TO <accumulator> END-READ / END-PERFORM')."
    )


def verify_file_accumulator_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """High-level entry point for the file-processing pattern.
    IMPORTANT, unlike the other four patterns: modern_fn must know the
    SYNTHETIC convention -- a parameter named 'record_count' (the
    unknown number of records) and a parameter whose name matches the
    Python name of the accumulated record field (the values of that
    field across all records, as an array)."""
    legacy_spec = extract_cobol_file_accumulator_loop(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    modern_spec = extract_python_accumulator_loop(modern_fn)

    if legacy_spec.table_name != modern_spec.table_name:
        raise UnsupportedLoopPattern(
            f"Table name (= record field name) does not match: COBOL '{legacy_spec.table_name}' "
            f"vs. Python '{modern_spec.table_name}'"
        )
    if legacy_spec.bound_name != modern_spec.bound_name:
        raise UnsupportedLoopPattern(
            f"Bound name does not match: expected 'record_count' (convention), "
            f"Python side uses '{modern_spec.bound_name}'"
        )

    proven, counterexample_k = prove_accumulator_loops_equivalent(legacy_spec, modern_spec)
    return {
        "label": "PROVEN" if proven else "FLAGGED FOR MANUAL REVIEW",
        "legacy_spec": legacy_spec,
        "modern_spec": modern_spec,
        "counterexample_k": counterexample_k,
    }


def extract_cobol_file_nested_accumulator_loop(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """A SIXTH pattern: a nested file-processing loop --
    'PERFORM UNTIL <eof> = <value> / READ <file> AT END MOVE <value> TO
    <eof> NOT AT END PERFORM VARYING <j> FROM 1 BY 1 UNTIL <j> > <fixed
    number> ADD <field>(<j>) TO <accumulator> END-PERFORM END-READ /
    END-PERFORM'. Structurally identical to the already solved "table of
    records with a fixed inner bound" pattern (NestedAccumulatorLoopSpec)
    -- the record count is again treated as an implicit, synthetic
    parameter 'record_count', with the fixed inner loop unrolled
    normally. No new proof concept -- it reuses the same machinery as
    the first (unconditional) file pattern."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit

    def raw(node):
        return node.ctx.start.getInputStream().getText(node.ctx.start.start, node.ctx.stop.stop)

    def find_perform_statements(paragraphs):
        found = []
        for p in paragraphs:
            for s in p.statements:
                if type(s).__name__ == "PerformStatement":
                    found.append(s)
        return found

    candidates = find_perform_statements(pu.procedure_division.root_paragraphs)
    for sec in pu.procedure_division.sections:
        candidates.extend(find_perform_statements(sec.paragraphs))

    for stmt in candidates:
        text = raw(stmt).strip()
        m = re.match(
            r"^PERFORM\s+UNTIL\s+([A-Za-z][A-Za-z0-9-]*)\s*=\s*([A-Za-z0-9][A-Za-z0-9-]*)\s+"
            r"READ\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+"
            r"AT\s+END\s+MOVE\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"NOT\s+AT\s+END\s+"
            r"PERFORM\s+VARYING\s+([A-Za-z][A-Za-z0-9-]*)\s+FROM\s+1\s+BY\s+1\s+UNTIL\s+"
            r"\6\s*>\s*(\d+)\s+"
            r"ADD\s+([A-Za-z][A-Za-z0-9-]*)\s*\(\s*\6\s*\)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"END-PERFORM\s+END-READ\s+END-PERFORM$",
            text, re.IGNORECASE | re.DOTALL,
        )
        if not m:
            continue
        (eof_field_1, eof_value_1, _file_name, eof_value_2, eof_field_2,
         _inner_var, inner_bound_text, record_field, accum_name) = m.groups()
        if eof_field_1.upper() != eof_field_2.upper() or eof_value_1.upper() != eof_value_2.upper():
            continue

        paragraph_statements = None
        for p in pu.procedure_division.root_paragraphs:
            if stmt in p.statements:
                paragraph_statements = p.statements
                break
        if paragraph_statements is None:
            for sec in pu.procedure_division.sections:
                for p in sec.paragraphs:
                    if stmt in p.statements:
                        paragraph_statements = p.statements
                        break
        stmt_idx = paragraph_statements.index(stmt)
        preceding = paragraph_statements[:stmt_idx]
        init_found = any(
            re.match(rf"^MOVE\s+0\s+TO\s+{re.escape(accum_name)}$", raw(s).strip(), re.IGNORECASE)
            for s in preceding if type(s).__name__ == "MoveStatement"
        )
        if not init_found:
            raise UnsupportedLoopPattern(
                f"Accumulator '{accum_name}' is not verifiably set to 0 before the loop "
                f"-- otherwise the base case of the induction proof would just be an assumption"
            )
        return NestedAccumulatorLoopSpec(
            outer_bound_name="record_count",  # SYNTHETIC -- fixed convention
            inner_bound=int(inner_bound_text),
            accumulator_name=_py_name(accum_name),
            table_name=_py_name(record_field),
            coeff=1,
        )

    raise UnsupportedLoopPattern(
        "No nested file-processing loop found that exactly matches the supported "
        "pattern ('PERFORM UNTIL <eof> = <value> / READ <file> AT END ... NOT AT END "
        "PERFORM VARYING <j> ... ADD <field>(<j>) TO <accumulator> END-PERFORM END-READ / END-PERFORM')."
    )


def verify_file_nested_accumulator_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """High-level entry point for the nested file pattern, analogous to
    verify_file_accumulator_loop. modern_fn must know the same
    convention: a parameter 'record_count' (number of records) and a
    parameter whose name matches the Python name of the accumulated
    record field, as a 2D table (table[i][j])."""
    legacy_spec = extract_cobol_file_nested_accumulator_loop(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    modern_spec = extract_python_nested_accumulator_loop(modern_fn)

    if legacy_spec.table_name != modern_spec.table_name:
        raise UnsupportedLoopPattern(
            f"Table name does not match: COBOL '{legacy_spec.table_name}' vs. Python '{modern_spec.table_name}'"
        )
    if legacy_spec.outer_bound_name != modern_spec.outer_bound_name:
        raise UnsupportedLoopPattern(
            f"Bound name does not match: expected 'record_count' (convention), "
            f"Python side uses '{modern_spec.outer_bound_name}'"
        )
    if legacy_spec.inner_bound != modern_spec.inner_bound:
        raise UnsupportedLoopPattern(
            f"Inner bound does not match: COBOL {legacy_spec.inner_bound} vs. Python {modern_spec.inner_bound}"
        )

    proven, counterexample_k = prove_nested_accumulator_loops_equivalent(legacy_spec, modern_spec)
    return {
        "label": "PROVEN" if proven else "FLAGGED FOR MANUAL REVIEW",
        "legacy_spec": legacy_spec,
        "modern_spec": modern_spec,
        "counterexample_k": counterexample_k,
    }


def extract_cobol_file_dual_accumulator_loop(cobol_source, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """A SEVENTH and final pattern for file loops: two simultaneous
    state variables -- 'PERFORM UNTIL <eof> = <value> / READ <file>
    AT END MOVE <value> TO <eof> NOT AT END ADD <field> TO <sum> ADD 1
    TO <counter> END-READ / END-PERFORM'. The most common real-world
    pattern for "compute sum AND count across all records" (e.g. for an
    average). Structurally identical to the already solved two-state
    pattern for PERFORM VARYING (DualAccumulatorLoopSpec) -- again no
    new proof concept, just a fourth extraction that reuses the same
    machinery."""
    params = _build_parser_params(source_format, copy_book_dirs)
    program = _analyze_cobol(cobol_source, params)
    pu = program.compilation_unit.program_unit

    def raw(node):
        return node.ctx.start.getInputStream().getText(node.ctx.start.start, node.ctx.stop.stop)

    def find_perform_statements(paragraphs):
        found = []
        for p in paragraphs:
            for s in p.statements:
                if type(s).__name__ == "PerformStatement":
                    found.append(s)
        return found

    candidates = find_perform_statements(pu.procedure_division.root_paragraphs)
    for sec in pu.procedure_division.sections:
        candidates.extend(find_perform_statements(sec.paragraphs))

    for stmt in candidates:
        text = raw(stmt).strip()
        m = re.match(
            r"^PERFORM\s+UNTIL\s+([A-Za-z][A-Za-z0-9-]*)\s*=\s*([A-Za-z0-9][A-Za-z0-9-]*)\s+"
            r"READ\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+"
            r"AT\s+END\s+MOVE\s+([A-Za-z0-9][A-Za-z0-9-]*)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"NOT\s+AT\s+END\s+"
            r"ADD\s+([A-Za-z][A-Za-z0-9-]*)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"ADD\s+1\s+TO\s+([A-Za-z][A-Za-z0-9-]*)\s+"
            r"END-READ\s+END-PERFORM$",
            text, re.IGNORECASE | re.DOTALL,
        )
        if not m:
            continue
        (eof_field_1, eof_value_1, _file_name, eof_value_2, eof_field_2,
         record_field, sum_accum_name, count_accum_name) = m.groups()
        if eof_field_1.upper() != eof_field_2.upper() or eof_value_1.upper() != eof_value_2.upper():
            continue

        paragraph_statements = None
        for p in pu.procedure_division.root_paragraphs:
            if stmt in p.statements:
                paragraph_statements = p.statements
                break
        if paragraph_statements is None:
            for sec in pu.procedure_division.sections:
                for p in sec.paragraphs:
                    if stmt in p.statements:
                        paragraph_statements = p.statements
                        break
        stmt_idx = paragraph_statements.index(stmt)
        preceding = paragraph_statements[:stmt_idx]

        def _init_ok(name):
            return any(
                re.match(rf"^MOVE\s+0\s+TO\s+{re.escape(name)}$", raw(s).strip(), re.IGNORECASE)
                for s in preceding if type(s).__name__ == "MoveStatement"
            )
        if not _init_ok(sum_accum_name) or not _init_ok(count_accum_name):
            raise UnsupportedLoopPattern(
                f"Both accumulators ('{sum_accum_name}', '{count_accum_name}') must be "
                f"verifiably set to 0 before the loop -- otherwise the base case would just be an assumption"
            )
        return DualAccumulatorLoopSpec(
            bound_name="record_count",  # SYNTHETIC -- fixed convention
            table_name=_py_name(record_field),
            sum_accum_name=_py_name(sum_accum_name),
            count_accum_name=_py_name(count_accum_name),
            sum_coeff=1,
        )

    raise UnsupportedLoopPattern(
        "No file-processing loop with two simultaneous state variables found that "
        "exactly matches the supported pattern ('PERFORM UNTIL <eof> = <value> / READ "
        "<file> AT END ... NOT AT END ADD <field> TO <sum> ADD 1 TO <counter> END-READ / "
        "END-PERFORM')."
    )


def verify_file_dual_accumulator_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """High-level entry point for the two-state file pattern, analogous
    to verify_file_accumulator_loop."""
    legacy_spec = extract_cobol_file_dual_accumulator_loop(cobol_source, source_format=source_format, copy_book_dirs=copy_book_dirs)
    modern_spec = extract_python_dual_accumulator_loop(modern_fn)

    if legacy_spec.table_name != modern_spec.table_name:
        raise UnsupportedLoopPattern(
            f"Table name does not match: COBOL '{legacy_spec.table_name}' vs. Python '{modern_spec.table_name}'"
        )
    if legacy_spec.bound_name != modern_spec.bound_name:
        raise UnsupportedLoopPattern(
            f"Bound name does not match: expected 'record_count' (convention), "
            f"Python side uses '{modern_spec.bound_name}'"
        )

    proven, counterexample_k = prove_dual_accumulator_loops_equivalent(legacy_spec, modern_spec)
    return {
        "label": "PROVEN" if proven else "FLAGGED FOR MANUAL REVIEW",
        "legacy_spec": legacy_spec,
        "modern_spec": modern_spec,
        "counterexample_k": counterexample_k,
    }


def verify_file_processing_loop(cobol_source, modern_fn, source_format=CobolSourceFormatEnum.FIXED, copy_book_dirs=None):
    """Unified entry point for FILE-processing loops, analogous to
    verify_variable_bound_loop (which unifies the four PERFORM VARYING
    patterns) -- tries ALL FOUR supported file-accumulator patterns in
    turn (simple, conditional, nested, two simultaneous states) and uses
    the first one that matches. The caller no longer needs to know which
    of the four file patterns applies -- exactly the same unification
    that already existed for PERFORM VARYING, applied consistently to
    the file variant as well. Also returns 'pattern', naming which of
    the four patterns actually applied."""
    attempts = [
        ("file_single", verify_file_accumulator_loop),
        ("file_nested", verify_file_nested_accumulator_loop),
        ("file_dual", verify_file_dual_accumulator_loop),
    ]
    errors = []
    for name, fn in attempts:
        try:
            result = fn(cobol_source, modern_fn, source_format=source_format, copy_book_dirs=copy_book_dirs)
            result["pattern"] = name
            return result
        except UnsupportedLoopPattern as e:
            errors.append(f"  - {name}: {e}")

    raise UnsupportedLoopPattern(
        "No file-processing loop found that matches any of the supported patterns "
        "(simple, nested, two simultaneous states -- the conditional variant goes "
        "through the same extraction as 'simple'). Details:\n" + "\n".join(errors)
    )
