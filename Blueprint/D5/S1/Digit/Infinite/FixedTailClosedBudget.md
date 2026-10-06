# Fixed-tail closed budget

## Abstract

Fixed-tail closed budget.

**Theorem 1.1 (Finite affine endpoint certificate).**

Lean statement: `D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider finitely many affine observations. Each observation reads one of two terminal scalar coordinates, and both coordinates range over fixed closed intervals. The target for each observation is another closed interval.

For a scalar x and target interval [l,u], the excess is max(l-x, max(0,x-u)). The excess of an affine observation over a terminal interval is bounded by the larger excess at the two terminal endpoints.

The maximum of the finitely many endpoint excesses is nonnegative. A nonnegative budget admits a fixed pair of terminal values for every value in the two terminal hulls exactly when it is at least this maximum. At the threshold, every pair of terminal values in the hulls satisfies all observations simultaneously.

## References

- Truth anchor: `D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel](ClosedObservationCommonTailWidthModel.md)
