# -*- coding: utf-8 -*-
"""
Path 1.1: COBOL COMP-3 as a scaled integer with explicit field width (QF_LIA)

Shows a bug class that is STRUCTURALLY invisible when using real-number
arithmetic (the earlier prototype): silent field overflow on PIC 9(n)V99 COMP-3.

COBOL semantics (simplified, without a SIZE ERROR clause):
  A field PIC 9(5)V99 can hold values from 0.00 to 999.99... no: 5 digits
  total, 2 of which are decimal places -> value range 0.00 to 999.99? No:
  9(5)V99 means 5 digits BEFORE and 2 AFTER the decimal point? -> here: 5
  digits TOTAL including the 2 decimal places (COBOL convention), i.e. a
  value range of 0.00 to 999.99 with 3 integer + 2 decimal digits.
  Scaled (x100): integer range 0 .. 99999 (5 digits).
  On overflow, COBOL truncates the upper digits: result mod 100000.
"""

import z3


def comp3_truncate(scaled_value, total_digits):
    """Symbolic model of COBOL's silent field overflow:
    keeps only the lowest `total_digits` decimal digits (scaled)."""
    modulus = 10 ** total_digits
    return scaled_value % modulus


def build_scenario():
    # Realistic overflow scenario: line-item total = quantity x unit price,
    # result is written back into a PIC 9(5)V99 COMP-3 accumulator field.
    quantity = z3.Int("quantity")             # item count
    unit_price_scaled = z3.Int("unit_price_scaled")  # unit price in cents (x100)

    # Realistic value ranges (so the solver doesn't search nonsensical numbers)
    constraints = z3.And(
        quantity >= 1, quantity <= 5_000,                    # plausible order quantity
        unit_price_scaled >= 1, unit_price_scaled <= 99_999,  # PIC 9(5)V99, valid field value
    )

    # --- LEGACY: COBOL field PIC 9(5)V99 COMP-3, result is written back into
    #     the same field -> implicit overflow truncation above 5 digits
    raw = quantity * unit_price_scaled
    legacy_result = comp3_truncate(raw, total_digits=5)

    # --- MODERN (LLM migration, bug): translated to i64/Decimal without field
    #     width, numerically "more faithful", but does NOT replicate the COBOL overflow
    modern_result_buggy = raw  # no truncation -> "more correct" but not COBOL-faithful value

    # --- MODERN (correct): explicitly replicates the field width
    modern_result_correct = comp3_truncate(raw, total_digits=5)

    return constraints, quantity, unit_price_scaled, legacy_result, modern_result_buggy, modern_result_correct


def prove(label, constraints, legacy_expr, modern_expr, quantity, unit_price_scaled):
    print("=" * 78)
    print(label)
    print("-" * 78)
    solver = z3.Solver()
    solver.add(constraints)
    solver.add(legacy_expr != modern_expr)
    result = solver.check()
    if result == z3.unsat:
        print("  LABEL: PROVEN - no overflow case exists where the two diverge.")
    else:
        m = solver.model()
        q = m.evaluate(quantity).as_long()
        p = m.evaluate(unit_price_scaled).as_long()
        raw_val = q * p
        legacy_val = raw_val % 100_000
        print("  LABEL: FLAGGED - counterexample found:")
        print(f"    quantity = {q}, unit_price = {p/100:.2f}")
        print(f"    raw (untruncated total)                  = {raw_val} (= {raw_val/100:.2f})")
        print(f"    legacy (COMP-3, 5 digits, with overflow)  = {legacy_val} (= {legacy_val/100:.2f})")
        print(f"    -> legacy system shows {legacy_val/100:.2f}, migrated system would show {raw_val/100:.2f}")
    print()


if __name__ == "__main__":
    constraints, quantity, unit_price, legacy, modern_buggy, modern_correct = build_scenario()

    prove(
        "Comparison: LEGACY (with COMP-3 overflow truncation) vs. MODERN WITHOUT field-width modeling",
        constraints, legacy, modern_buggy, quantity, unit_price,
    )
    prove(
        "Comparison: LEGACY (with COMP-3 overflow truncation) vs. MODERN WITH correct field width",
        constraints, legacy, modern_correct, quantity, unit_price,
    )
