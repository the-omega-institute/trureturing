# Short denominator exclusion with literal Robin budgets

## Abstract

The literal Robin budgets exclude short denominators whenever the original integer box misses the window.

For an actual cutoff at X write L = log X. The three signed slopes are L divided by the second cutoff offset, and the third and fifth offsets divided by the second. The budget vector keeps the nested floor on the first axis and the ordinary floors on the other two. Its reference logarithm may differ from L by at most one.

**Theorem 1.1 (The literal floors give both label error bounds).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport.floor_budget_errors`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport.floor_budget_errors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 37/50 ≤ β < 3/4 and positive budget coefficient, each squared coordinate error is bounded by the full padded sum. The first and second axis budgets grow at least exponentially at rate 1/15 in L. The third layer retains its additional factor L squared. The explicit coefficient is common to both errors, uniformly over all signed integer labels.

**Theorem 1.2 (Every late box miss has a large primitive denominator).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport.exists_fixed_clock_box_miss_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport.exists_fixed_clock_box_miss_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three rounded budgets times the original window width tend uniformly to infinity on the unit reference neighborhood. The exact perturbed integer clock tends to infinity and stays in that neighborhood. The three-axis affine theorem then applies to the original closed integer box and strict window. Its unique primitive label retains the signed phase gap and weighted bound, and its denominator is strictly larger than L divided by 50 log L and at most the reciprocal of the window width.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport.exists_fixed_clock_box_miss_obstruction`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport.floor_budget_errors`
- Dependency: [D5/S3/Arith/DiophantineApproximation/AffineCongruenceIntegerBoxThreeCover](../../DiophantineApproximation/AffineCongruenceIntegerBoxThreeCover.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualModeThreeShortDenominator](ActualModeThreeShortDenominator.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock](FixedBIntegerClock.md)
