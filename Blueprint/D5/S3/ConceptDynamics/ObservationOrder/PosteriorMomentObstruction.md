# An obstruction to posterior moment realizability

## Abstract

A rational five-target candidate moment satisfies centered matrix positivity and fails finite posterior realizability.

**Definition 1.1 (Candidate sufficient conditions at a uniform prior).**

Lean statement: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.claim`

*Formalization.* `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prior puts mass one fifth on each of five targets. The claim asks whether every symmetric real matrix with nonnegative entries, row sums equal to the prior, and positive semidefinite centered part is a finite mixture of posterior outer products. The mixture masses and the coordinates of each posterior vector are nonnegative and sum to one over their respective index sets. The row sums determine the mixture barycenter.

**Theorem 1.2 (A five-cycle moment refutes the claim).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Index the targets by a cycle of length five. The proposed moment has diagonal entries 5/55, entries 3/55 on adjacent pairs, and zero elsewhere. Its row sums are 1/5. An exact sum of four squares gives the quadratic form of its centered part and establishes positive semidefiniteness.

Zero entries on nonedges force every positive-mass posterior to have support in a clique of the cycle. Each clique has at most two vertices. On such a support, the sum of squares is at least twice the sum of products along cycle edges. Summing over posterior components would bound twice the edge sum by the trace. The proposed moment has twice the edge sum 30/55 and trace 25/55.

The conclusion concerns finite mixtures and this specified uniform prior. The contradiction holds for any finite number of nonnegative factors, with or without their normalization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.claim`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.result`
