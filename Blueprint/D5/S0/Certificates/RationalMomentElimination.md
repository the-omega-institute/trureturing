# Rational support elimination certificates

## Abstract

A proposed null direction is checked using exact rational identities and cross-multiplied ratio inequalities. Acceptance implies nonnegative weights, unchanged moments, and strict support descent.

**Definition 1.1 (Computable raw-vector support).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.activeAtoms`

*Formalization.* `D5/S0/Certificates/RationalMomentElimination.activeAtoms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Enumerates exactly the nonzero weights before packaging the vector as a normalized finite response law.

**Definition 1.2 (Data-only elimination payload).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.EliminationStep`

*Formalization.* `D5/S0/Certificates/RationalMomentElimination.EliminationStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The payload contains a rational direction array and one pivot index. It contains no proof fields or trusted solver output.

**Definition 1.3 (Finite arithmetic validity conditions).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.ValidStep`

*Formalization.* `D5/S0/Certificates/RationalMomentElimination.ValidStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Checks nonnegative input, positive pivot, zero normalization and feature directions, no motion at inactive atoms, and all ratio comparisons.

**Definition 1.4 (Exact executable validator).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.checkStep`

*Formalization.* `D5/S0/Certificates/RationalMomentElimination.checkStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decides the finite rational conditions. No threshold or floating-point comparison is used.

**Theorem 1.5 (Validator characterization).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.checkStep_eq_true_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.checkStep_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean acceptance is equivalent to the semantic arithmetic conditions used by the preservation proofs.

**Definition 1.6 (Rational boundary update).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.eliminate`

*Formalization.* `D5/S0/Certificates/RationalMomentElimination.eliminate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracts the pivot ratio times the direction. The checked pivot has a strictly positive denominator.

**Theorem 1.7 (Retain nonnegative weights).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.validStep_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.validStep_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive direction coordinates are bounded by the certified pivot ratio; nonpositive direction coordinates cannot lower the weights.

**Theorem 1.8 (Preserve total mass).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.validStep_total`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.validStep_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The direction sums to zero, so the rational update preserves total mass exactly.

**Theorem 1.9 (Preserve every retained moment).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.validStep_moment`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.validStep_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uses the existing linearObjective semantics. Every checked zero directional moment remains unchanged after the update.

**Theorem 1.10 (Respect hard support exclusions).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.validStep_zero_stays_zero`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.validStep_zero_stays_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An initially zero atom cannot acquire mass. The condition is separate from preservation of the nominated moments.

**Theorem 1.11 (Remove the chosen pivot exactly).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.validStep_pivot_zero`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.validStep_pivot_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pivot weight cancels identically at the selected ratio, without numerical tolerances.

**Theorem 1.12 (Strict support descent).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.validStep_support`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.validStep_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The new support is a subset of the old support with strictly smaller cardinality. Ties may remove several atoms.

**Theorem 1.13 (Maximal feasible move along the direction).**

Lean statement: `D5/S0/Certificates/RationalMomentElimination.validStep_maximal_rate`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentElimination.validStep_maximal_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any larger move makes the certified pivot negative. This is a linewise maximality statement, not an optimality claim for the causal query.

## References

- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.EliminationStep`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.ValidStep`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.activeAtoms`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.checkStep`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.checkStep_eq_true_iff`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.eliminate`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.validStep_maximal_rate`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.validStep_moment`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.validStep_nonnegative`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.validStep_pivot_zero`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.validStep_support`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.validStep_total`
- Truth anchor: `D5/S0/Certificates/RationalMomentElimination.validStep_zero_stays_zero`
- Dependency: [D5/S0/Certificates/LinearObjectiveDual](LinearObjectiveDual.md)
