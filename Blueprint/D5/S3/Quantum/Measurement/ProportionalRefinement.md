# Proportional refinement and the actual defect

## Abstract

Normalized proportional pieces conserve quadratic budgets, contract quartic budgets, and preserve a channel when the same feedback Kraus operator is used on every piece.

**Theorem 1.1 (Quadratic budgets are conserved).**

$$\forall t, sumWeights=1 \Rightarrow quadraticBudgets$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ProportionalRefinement.quadratic_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite coefficient family t with sum of squared moduli equal to one, each degree-two budget sums back to its unrefined value. The three readouts represent the defect, actual trace-defect budget, and the weighted ratio in the proposition.

**Theorem 1.2 (The concrete squared-distance budget is conserved).**

$$\forall p, q \Rightarrow sumMinWeights=minBudget$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ProportionalRefinement.min_coordinate_budget_preserved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source distance budget is min(p,q). Each proportional piece scales both coordinates by the same nonnegative squared modulus, so the finite sum of the minima returns the original minimum.

**Theorem 1.3 (Quartic budgets contract).**

$$\forall t, sumWeights=1 \Rightarrow quarticBudgets$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ProportionalRefinement.quartic_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The products of two quadratic coordinate weights and an arbitrary quartic budget are multiplied by the fourth-power sum. The finite fourth-power sum is at most one by the normalized squared-modulus condition.

**Theorem 1.4 (Common-feedback Kraus refinement preserves the channel).**

$$\forall t, sumWeights=1 \Rightarrow channelPreserved$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ProportionalRefinement.actual_channel_preserved_rectangular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every proportional spectral piece retains the same feedback, its Kraus operator is the corresponding scalar multiple of the original. Summing the resulting conjugations recovers the original matrix channel for every input.

**Theorem 1.5 (Rank-one completeness is preserved entrywise).**

$$\forall i, j, sumOuterPieces=outerVector$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ProportionalRefinement.completeness_preserved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of coordinates, the outer-product contribution of the proportional pieces sums to the original rank-one contribution. This is the entrywise completeness identity used by a finite POVM refinement.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ProportionalRefinement.actual_channel_preserved_rectangular`
- Truth anchor: `D5/S3/Quantum/Measurement/ProportionalRefinement.completeness_preserved`
- Truth anchor: `D5/S3/Quantum/Measurement/ProportionalRefinement.min_coordinate_budget_preserved`
- Truth anchor: `D5/S3/Quantum/Measurement/ProportionalRefinement.quadratic_budgets`
- Truth anchor: `D5/S3/Quantum/Measurement/ProportionalRefinement.quartic_budgets`
