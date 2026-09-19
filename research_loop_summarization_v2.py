"""
RESEARCH PROTOTYPE v2 -- manually structured induction.

Lesson from v1 (research_loop_summarization.py): neither plain RecFunction +
Solver.check() nor expecting Z3 to "find" an induction on its own works in
practice (timeout even in the TRIVIAL control case).

The reason: Z3 (like any SMT solver) does not PROVE an induction by itself --
it only checks whether a given FORMULA is (un)satisfiable. Mathematical
induction has to be structured by the CALLER, as TWO SEPARATE, each
NON-RECURSIVE, queries:
  1. Base case: do both functions agree at n=0?
  2. Induction step: IF they agree at an arbitrary k (induction hypothesis,
     added as an assumption/axiom), does it follow that they also agree at
     k+1? This is ONE unfolding step of the recursion, not unbounded
     recursion anymore -- this should be trivial for Z3.

If BOTH queries come back UNSAT (no counterexample), the equivalence is
proven for ALL n >= 0 -- via classical induction, not via Z3's "magic".
"""
import z3


def prove_by_induction(name, base_legacy, base_modern, step_legacy_expr, step_modern_expr, k, s_legacy_k, s_modern_k):
    """General scaffold: base_* are the values at n=0 (Python values or
    Z3 expressions without recursion). step_*_expr are Z3 expressions for
    f(k+1) IN TERMS OF s_legacy_k/s_modern_k (the values at k already
    ASSUMED equal) -- this is the actual trick: the induction hypothesis is
    assumed as an EQUALITY, not proven anew."""
    print(f"--- {name} ---")

    # 1. Base case
    solver_base = z3.Solver()
    solver_base.add(base_legacy != base_modern)
    res_base = solver_base.check()
    base_ok = res_base == z3.unsat
    print(f"  Base case (n=0): {res_base} ({'OK' if base_ok else 'FAILED'})")

    # 2. Induction step: s_legacy_k == s_modern_k is assumed as a hypothesis
    # (not proven!), then it's checked whether f(k+1) stays equal for both --
    # this is a SINGLE unfolding step, not unbounded recursion.
    solver_step = z3.Solver()
    solver_step.add(k >= 0)
    solver_step.add(s_legacy_k == s_modern_k)  # induction hypothesis, as an assumption
    solver_step.add(step_legacy_expr != step_modern_expr)  # search for a counterexample to the step
    res_step = solver_step.check()
    step_ok = res_step == z3.unsat
    print(f"  Induction step (k -> k+1): {res_step} ({'OK' if step_ok else 'FAILED'})")
    if not step_ok:
        m = solver_step.model()
        print(f"    Counterexample: k={m.eval(k)}")

    overall = base_ok and step_ok
    print(f"  => {'PROVEN for ALL n >= 0 (by induction)' if overall else 'NOT proven'}\n")
    return overall


def experiment_1_identical():
    """Two structurally identical summation loops."""
    table = z3.Array("table", z3.IntSort(), z3.IntSort())
    k = z3.Int("k")
    s_legacy_k = z3.Int("s_legacy_k")
    s_modern_k = z3.Int("s_modern_k")
    # f(k+1) = f(k) + table[k] -- identical for BOTH
    step_legacy = s_legacy_k + table[k]
    step_modern = s_modern_k + table[k]
    return prove_by_induction("Experiment 1: identical recursion",
                               z3.IntVal(0), z3.IntVal(0),
                               step_legacy, step_modern, k, s_legacy_k, s_modern_k)


def experiment_2_off_by_one_bug():
    """Bug: 'modern' adds table[k+1] instead of table[k] (index shift)."""
    table = z3.Array("table", z3.IntSort(), z3.IntSort())
    k = z3.Int("k")
    s_legacy_k = z3.Int("s_legacy_k")
    s_modern_k = z3.Int("s_modern_k")
    step_legacy = s_legacy_k + table[k]
    step_modern = s_modern_k + table[k + 1]  # BUG: wrong index
    return prove_by_induction("Experiment 2: index-shift bug (MUST fail)",
                               z3.IntVal(0), z3.IntVal(0),
                               step_legacy, step_modern, k, s_legacy_k, s_modern_k)


def experiment_3_different_but_equal():
    """Two DIFFERENTLY formulated steps that are mathematically equal
    (e.g. a different but equivalent arithmetic rearrangement)."""
    table = z3.Array("table", z3.IntSort(), z3.IntSort())
    k = z3.Int("k")
    s_legacy_k = z3.Int("s_legacy_k")
    s_modern_k = z3.Int("s_modern_k")
    step_legacy = s_legacy_k + table[k]
    step_modern = table[k] + s_modern_k  # only the order is swapped -- mathematically equal
    return prove_by_induction("Experiment 3: rearranged but equivalent",
                               z3.IntVal(0), z3.IntVal(0),
                               step_legacy, step_modern, k, s_legacy_k, s_modern_k)


if __name__ == "__main__":
    r1 = experiment_1_identical()
    r2 = experiment_2_off_by_one_bug()
    r3 = experiment_3_different_but_equal()
    print("=" * 78)
    print(f"Experiment 1 (identical, should be PROVEN):            {'OK' if r1 else 'FAILED'}")
    print(f"Experiment 2 (bug, should NOT be proven):              {'OK' if not r2 else 'FAILED'}")
    print(f"Experiment 3 (equivalent, should be PROVEN):           {'OK' if r3 else 'FAILED'}")
