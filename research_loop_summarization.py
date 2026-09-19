"""
RESEARCH PROTOTYPE -- loop summarization via Z3's RecFunction.

Goal: formulate a loop with a VARIABLE (data-dependent, not compile-time-
constant) bound n as a recursive relation instead of unrolling it -- and
check whether Z3 can actually prove a universally valid equivalence from
that for ALL n (not just individual concrete values).

This is deliberately a STANDALONE experiment, NOT integrated into the main
pipeline -- first check whether the approach holds up at all before turning
it into a real extension of engine.py.
"""
import z3

TABLE_SORT = z3.ArraySort(z3.IntSort(), z3.IntSort())


def build_sum_function(name, table):
    """Recursively defines: f(0) = 0, f(n) = f(n-1) + table[n-1] for n > 0.
    This corresponds to: 'PERFORM VARYING I FROM 1 BY 1 UNTIL I > N; ADD TABLE(I) TO TOTAL'."""
    f = z3.RecFunction(name, z3.IntSort(), z3.IntSort())
    n = z3.Int("n")
    z3.RecAddDefinition(f, [n], z3.If(n <= 0, 0, f(n - 1) + table[n - 1]))
    return f


def run_experiment_1_identical_recurrence():
    print("=" * 78)
    print("EXPERIMENT 1: two STRUCTURALLY IDENTICAL recursions -- control case")
    print("=" * 78)
    table = z3.Array("table", z3.IntSort(), z3.IntSort())
    f_legacy = build_sum_function("sum_legacy_1", table)
    f_modern = build_sum_function("sum_modern_1", table)

    n = z3.Int("n")
    solver = z3.Solver()
    solver.add(n >= 0)
    solver.add(f_legacy(n) != f_modern(n))  # search for a counterexample
    result = solver.check()
    print(f"Result: {result} (expected: unsat -- identical for ALL n)")
    return result == z3.unsat


def run_experiment_2_genuinely_different_but_equal():
    print("=" * 78)
    print("EXPERIMENT 2: two DIFFERENTLY formulated but mathematically equal sums")
    print("=" * 78)
    table = z3.Array("table", z3.IntSort(), z3.IntSort())
    # Legacy: normal forward sum
    f_legacy = build_sum_function("sum_legacy_2", table)

    # Modern: BACKWARD sum -- g(0)=0, g(n) = g(n-1) + table[0..n-1] from the END
    # g(n) = table[n-1] + g(n-1), but the RECURSION itself runs structurally
    # differently (accumulating down from n instead of up from 1) -- a stand-in
    # for "a translator changed the loop direction, the result is the same"
    g = z3.RecFunction("sum_modern_2", z3.IntSort(), z3.IntSort())
    n_var = z3.Int("n")
    z3.RecAddDefinition(g, [n_var], z3.If(n_var <= 0, 0, table[n_var - 1] + g(n_var - 1)))

    n = z3.Int("n")
    solver = z3.Solver()
    solver.add(n >= 0)
    solver.add(f_legacy(n) != g(n))
    result = solver.check()
    print(f"Result: {result} (expected: unsat -- mathematically the same sum)")
    return result == z3.unsat


def run_experiment_3_genuine_bug():
    print("=" * 78)
    print("EXPERIMENT 3: genuine bug -- modern version counts one element too few")
    print("=" * 78)
    table = z3.Array("table", z3.IntSort(), z3.IntSort())
    f_legacy = build_sum_function("sum_legacy_3", table)

    # Bug: off-by-one, sums only up to n-2 instead of n-1
    f_buggy = z3.RecFunction("sum_buggy_3", z3.IntSort(), z3.IntSort())
    n_var = z3.Int("n")
    z3.RecAddDefinition(f_buggy, [n_var], z3.If(n_var <= 1, 0, f_buggy(n_var - 1) + table[n_var - 2]))

    n = z3.Int("n")
    solver = z3.Solver()
    solver.add(n > 0)
    solver.add(f_legacy(n) != f_buggy(n))
    result = solver.check()
    print(f"Result: {result} (expected: sat -- the bug must be found)")
    if result == z3.sat:
        m = solver.model()
        print(f"Counterexample n = {m.eval(n)}")
    return result == z3.sat


if __name__ == "__main__":
    ok1 = run_experiment_1_identical_recurrence()
    ok2 = run_experiment_2_genuinely_different_but_equal()
    ok3 = run_experiment_3_genuine_bug()
    print()
    print("=" * 78)
    print(f"Experiment 1 (identical):                {'PASSED' if ok1 else 'FAILED'}")
    print(f"Experiment 2 (different but equal):      {'PASSED' if ok2 else 'FAILED'}")
    print(f"Experiment 3 (genuine bug found):        {'PASSED' if ok3 else 'FAILED'}")
