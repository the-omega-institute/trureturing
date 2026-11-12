# The actual PSD overlap optimization and Hermitian trace uniqueness

## Abstract

The actual PSD overlap optimization and Hermitian trace uniqueness

The common-PSD overlap is a finite matrix optimization, including zero matrices and the empty index type. Its operational interpretation is established by MaximalHockeyStickOperational, following HMT Proposition V.1. The Hermitian relaxation used internally is a different feasible set and is not silently assumed positive.

**Definition 1.1 (positiveOverlaps).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.positiveOverlaps`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.positiveOverlaps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

positiveOverlaps A B consists exactly of matrices X with 0 <= X, X <= A and X <= B in Loewner order. Both upper bounds are retained. Profile, support localization and actual reverse preparations consume this feasible set.

**Definition 1.2 (overlapValue).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.overlapValue`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.overlapValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

overlapValue A B is the real supremum of Re Tr(X) over positiveOverlaps A B. Compactness and a zero feasible point supply attainment for PSD A,B; no normalization is imposed. maximalHockey and the operational representation consume this objective.

**Definition 1.3 (maximalHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.maximalHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.maximalHockey` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

maximalHockey A B t is Re Tr(A) minus overlapValue A (t B). This definition is an SDP expression. Operational.operational_hockey_eq proves its equality to the infimum of the actual sums max(p_i-t q_i,0) for t>0; the general convex kernel consumes that bridge.

**Theorem 1.4 (overlap attained).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.overlap_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.overlap_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every PSD A,B there exists an actual positive common lower bound whose real trace equals overlapValue A B. The closed feasible set is bounded by A, hence compact in finite dimension. Profile regularity and the three-component operational construction use the maximizing matrix, including singular and zero cases.

**Theorem 1.5 (positive residual unique).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.positive_residual_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.positive_residual_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For Hermitian H and PSD T with T-H also PSD, Re Tr(H_+) <= Re Tr(T); equality forces T=H_+. The proof diagonalizes H, bounds each diagonal residual, and eliminates zero diagonal columns by positivity. The Hermitian common-lower-bound uniqueness theorem consumes this rigidity.

**Theorem 1.6 (hermitian overlap unique).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.hermitian_overlap_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.hermitian_overlap_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For Hermitian U,V, X0=U-(U-V)_+ is Hermitian and below both. Every Hermitian X below both has trace at most Tr(X0), with equality only for X=X0. No claim that X0 is PSD is made. Threshold uses this uniqueness after the interior positivity constraint has been removed.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.hermitian_overlap_unique`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.maximalHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.overlapValue`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.overlap_attained`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.positiveOverlaps`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.positive_residual_unique`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickInterior](MaximalHockeyStickInterior.md)
