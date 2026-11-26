# Distance to a realizable five-target posterior moment

## Abstract

A two-orbit posterior mixture attains the exact squared Frobenius distance at a fixed uniform prior.

**Definition 1.1 (Five-cycle input family).**

Lean statement: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.cycleMoment`

*Formalization.* `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.cycleMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real t, the matrix on Fin 5 has diagonal entries 1/5 − 2t, entries t on adjacent pairs modulo five, and zero entries on distinct nonadjacent pairs.

**Definition 1.2 (Projected moment).**

Lean statement: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.projectedMoment`

*Formalization.* `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.projectedMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real t, put delta = 20t − 1. The matrix on Fin 5 has diagonal entries 1/10 − delta/15, edge entries 1/20, and distinct nonedge entries delta/30.

**Definition 1.3 (Squared Frobenius distance).**

Lean statement: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.squaredDistance`

*Formalization.* `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.squaredDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For two real matrices on Fin 5, sum the squared differences over all 25 ordered entries.

**Definition 1.4 (Finite moment at the uniform prior).**

Lean statement: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.IsUniformPosteriorMoment`

*Formalization.* `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.IsUniformPosteriorMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real matrix on Fin 5 is a finite mixture of outer products of probability vectors. The mixture masses are nonnegative and sum to one. Its weighted vector mean is 1/5 at each of the five coordinates.

**Theorem 1.5 (Exact distance and unique minimizer).**

Lean statement: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.projected_moment_unique`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.projected_moment_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t with 1/20 ≤ t ≤ 11/160, the projected moment is feasible at the uniform prior, and its squared Frobenius distance to the cycle input equals (20t − 1)²/24. Every finite posterior moment at that prior has squared distance at least this value. Equality implies that the moment is the projected matrix.

Average the outer products of the five cyclic shifts of (1/2, 1/2, 0, 0, 0) and of (1/4, 1/2, 1/4, 0, 0). Give the second orbit mass 8(20t − 1)/3 and the first orbit the complementary mass. Each orbit has uniform mean, and their weighted outer products give the projected entries.

The five-cycle edge-product sum of any probability vector is at most 1/4, the five-cycle case of Motzkin–Straus, Section 1, Theorem 1. Averaging gives a supporting inequality on moments with arbitrary nonedge entries. The input-to-projection difference is parallel to its normal. The squared-distance expansion leaves a nonnegative cross term and the squared distance to the projected matrix, which gives the minimum and uniqueness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.IsUniformPosteriorMoment`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.cycleMoment`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.projectedMoment`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.projected_moment_unique`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance.squaredDistance`
