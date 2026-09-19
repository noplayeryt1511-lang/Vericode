# -*- coding: utf-8 -*-
"""
Path 1.2: A concolic engine instead of pure random fuzzing.

Idea (classic DART/CUTE style): functions are executed COMPLETELY NORMALLY
and concretely - but with "concolic" values (Concrete + Symbolic coupled
together). Every branch (if/while) calls __bool__(), and that is exactly
where we record the path condition. Afterward, Z3 selectively negates
individual conditions from the recorded path and solves for new inputs that
force a DIFFERENT path - instead of blindly guessing as pure fuzzing does.

The decisive advantage over the SymbolicEvaluator in engine.py: this also
works for unbounded while loops and arbitrary Python code, because only the
path ACTUALLY TAKEN by a concrete execution is recorded (no upfront
unrolling needed) - this is exactly the class of code that causes the
SymbolicEvaluator to raise UnsupportedConstruct.
"""

import inspect
import operator
import random

import z3


class PathTracer:
    """Collects the path conditions of ONE concrete execution, in order."""
    def __init__(self):
        self.constraints = []  # list of z3.BoolExpr, already oriented to the branch taken

    def record(self, symbolic_cond, taken: bool):
        self.constraints.append(symbolic_cond if taken else z3.Not(symbolic_cond))


class CBool:
    """Result of a concolic comparison: concrete bool + symbolic condition.
    __bool__ is called automatically by Python on if/while - that is exactly
    where we write into the active PathTracer."""
    __slots__ = ("c", "s", "tracer")

    def __init__(self, c, s, tracer):
        self.c = c
        self.s = s
        self.tracer = tracer

    def __bool__(self):
        self.tracer.record(self.s, self.c)
        return self.c


def _split(x):
    """Returns (concrete, symbolic) for either a CVal or a plain Python int."""
    if isinstance(x, CVal):
        return x.c, x.s
    return x, z3.IntVal(x)


class CVal:
    """A value carried in parallel, both concretely AND symbolically."""
    __slots__ = ("c", "s", "tracer")

    def __init__(self, c, s, tracer):
        self.c = c
        self.s = s
        self.tracer = tracer

    def _arith(self, other, cop, sop):
        oc, os = _split(other)
        return CVal(cop(self.c, oc), sop(self.s, os), self.tracer)

    def _cmp(self, other, cop, sop):
        oc, os = _split(other)
        return CBool(cop(self.c, oc), sop(self.s, os), self.tracer)

    def __add__(self, other): return self._arith(other, operator.add, operator.add)
    __radd__ = __add__

    def __sub__(self, other): return self._arith(other, operator.sub, operator.sub)
    def __rsub__(self, other): return CVal(other, z3.IntVal(other), self.tracer).__sub__(self)

    def __mul__(self, other): return self._arith(other, operator.mul, operator.mul)
    __rmul__ = __mul__

    def __floordiv__(self, other):
        return self._arith(other, operator.floordiv, lambda a, b: a / b)

    def __mod__(self, other):
        return self._arith(other, operator.mod, lambda a, b: a % b)

    def __neg__(self):
        return CVal(-self.c, -self.s, self.tracer)

    def __lt__(self, other): return self._cmp(other, operator.lt, operator.lt)
    def __le__(self, other): return self._cmp(other, operator.le, operator.le)
    def __gt__(self, other): return self._cmp(other, operator.gt, operator.gt)
    def __ge__(self, other): return self._cmp(other, operator.ge, operator.ge)
    def __eq__(self, other): return self._cmp(other, operator.eq, lambda a, b: a == b)
    def __ne__(self, other): return self._cmp(other, operator.ne, lambda a, b: a != b)

    def __hash__(self):
        return hash(self.c)

    def __repr__(self):
        return f"CVal({self.c})"


def concolic_run(func, concrete_args, param_names, tracer):
    """Runs func COMPLETELY NORMALLY with Python, but with CVal arguments
    instead of plain ints. Returns (concrete return value, tracer with path
    conditions)."""
    consts = {name: z3.Const(name, z3.IntSort()) for name in param_names}
    wrapped = [CVal(v, consts[name], tracer) for v, name in zip(concrete_args, param_names)]
    result = func(*wrapped)
    return result.c if isinstance(result, CVal) else result, consts


def _param_names(func):
    return list(inspect.signature(func).parameters.keys())


class ConcolicResult:
    def __init__(self, found_diff, counterexample=None, iterations=0, paths_explored=0, note=""):
        self.found_diff = found_diff
        self.counterexample = counterexample
        self.iterations = iterations
        self.paths_explored = paths_explored
        self.note = note


def concolic_search(legacy_fn, modern_fn, seed=None, max_iterations=200, bound=(-10_000, 10_000),
                     max_branch_points_per_trace=40, hard_trace_length_cap=300):
    """Drives the concolic exploration: starts from a seed input, runs LEGACY
    and MODERN concolically, compares the concrete outputs, and, on a match,
    selectively negates path conditions (from BOTH traces) to have Z3 solve
    for an input that reaches a previously unexplored branch.

    bound: fallback value range for parameters that are not constrained in
    either trace (prevents Z3 from returning astronomically large numbers).

    max_branch_points_per_trace: a known scalability issue with naive
    concolic testing - every loop iteration produces its OWN branch point in
    the trace. For a while loop already several thousand steps long,
    negating EVERY single point would lead to O(n^2) solver calls
    (empirically observed: timeout at ~8500 iterations when trying ALL
    indices).

    IMPROVEMENT (empirically verified, not just assumed): a SINGLE negation
    at a deep index (~400) only costs about ~17ms - the actual cost problem
    was never a single deep index, but rather trying to negate ALL thousands
    of indices in a long trace. For traces over max_branch_points_per_trace,
    the whole trace is therefore no longer discarded; instead only a FIXED
    slice is negated (the last and first few entries - empirically often the
    most informative, because special-case logic tends to sit right AFTER a
    loop). The divergence check (out_l != out_m) still always runs over the
    FULL, untruncated trace.

    KNOWN LIMITATION THAT REMAINS: this is a heuristic (fixed start/end
    slice), not true loop summarization/widening. A bug that appears ONLY in
    the MIDDLE of a very long loop (not at the start or right after the end)
    will still be missed. For the case found in test_fuzzing_limit.py
    (trigger right after loop end), this fix demonstrably helps - see
    test_loop_summarization.py.

    bound: either a single (lo, hi) tuple (the same for ALL parameters) OR a
    dict {"paramname": (lo, hi), ...} for different bounds per parameter
    (e.g. quantity 0-9999, price 0-999999) - compatible with the
    merged_bounds format from engine.py's resolve_input_bounds()."""
    params = _param_names(legacy_fn)
    assert params == _param_names(modern_fn)

    if isinstance(bound, dict):
        param_bounds = {p: bound.get(p, (-10_000, 10_000)) for p in params}
    else:
        param_bounds = {p: bound for p in params}

    if seed is None:
        seed = tuple(random.randint(*param_bounds[p]) for p in params)

    worklist = [seed]
    tried = set()
    paths_explored = 0
    skipped_long_traces = 0
    iteration = 0

    for iteration in range(1, max_iterations + 1):
        if not worklist:
            break
        args = worklist.pop(0)
        if args in tried:
            continue
        tried.add(args)
        paths_explored += 1

        tracer_l = PathTracer()
        tracer_m = PathTracer()
        try:
            out_l, consts_l = concolic_run(legacy_fn, args, params, tracer_l)
        except (MemoryError, RecursionError):
            # Do NOT silently skip severe errors -- that would mean a
            # memory-bomb/stack-overflow candidate gets treated as "just one
            # candidate among many, try the next one", and the search would
            # incorrectly report "no difference found" even though the code
            # itself is fundamentally broken.
            # Real-world example that exposed exactly this: see test_sandbox.py.
            raise
        except Exception:
            continue
        try:
            out_m, consts_m = concolic_run(modern_fn, args, params, tracer_m)
        except (MemoryError, RecursionError):
            raise
        except Exception:
            continue

        if out_l != out_m:
            return ConcolicResult(
                found_diff=True,
                counterexample=dict(zip(params, args)),
                iterations=iteration,
                paths_explored=paths_explored,
                note=f"Divergence found after {iteration} concolic iterations "
                     f"({paths_explored} distinct paths explored, "
                     f"{skipped_long_traces} overly long traces skipped for candidate generation).",
            )

        # Generate new candidates: for every recorded path condition (from
        # either the legacy or modern trace) -> negate exactly THIS one
        # condition, keep the rest of the prefix fixed, solve with Z3 for
        # new concrete values.
        for trace, consts in ((tracer_l.constraints, consts_l), (tracer_m.constraints, consts_m)):
            if len(trace) <= max_branch_points_per_trace:
                indices_to_try = range(len(trace))
            elif len(trace) > hard_trace_length_cap:
                # Even the sliding-window slice remains too expensive for
                # VERY long traces (cost per negation scales linearly with
                # the prefix size, ~16us/entry measured empirically -> with
                # tens of thousands of entries and many outer iterations
                # this adds up to minutes). Skip entirely here, falling back
                # to the old behavior as a safety net.
                skipped_long_traces += 1
                continue
            else:
                skipped_long_traces += 1
                half = max(1, min(10, max_branch_points_per_trace // 2))
                indices_to_try = list(range(half)) + list(range(len(trace) - half, len(trace)))
            for i in indices_to_try:
                solver = z3.Solver()
                solver.add(*trace[:i])
                solver.add(z3.Not(trace[i]))
                for name in params:
                    lo, hi = param_bounds[name]
                    solver.add(consts[name] >= lo, consts[name] <= hi)
                if solver.check() == z3.sat:
                    model = solver.model()
                    candidate = tuple(
                        model.evaluate(consts[name], model_completion=True).as_long()
                        for name in params
                    )
                    if candidate not in tried:
                        worklist.append(candidate)

    return ConcolicResult(
        found_diff=False,
        iterations=iteration,
        paths_explored=paths_explored,
        note=f"No difference found over {paths_explored} specifically explored paths "
             f"(after a budget of {max_iterations} iterations, {skipped_long_traces} overly "
             f"long traces skipped). Not a mathematical proof - residual risk remains.",
    )
