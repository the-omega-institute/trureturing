# The diagonal difference bound

## Abstract

A positive block overlap controls the squared difference of trace-one diagonal blocks.

**Theorem 1.1 (The normalized overlap is at most one).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.normalized_trace_norm_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.normalized_trace_norm_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every finite coordinate type and complex blocks A, X and B with positive semidefinite block matrix [A X; X-adjoint B] and tr A=tr B=1, the modulus |tr X| is at most one. Summing the coordinate block compressions gives a positive two-by-two matrix with diagonal entries one and off-diagonal entry tr X. Its positive semidefinite entry bound gives the required modulus bound.

**Theorem 1.2 (A squared Loewner bound from the block overlap).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.normalized_difference_square_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.normalized_difference_square_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

Let W=[A X; X-adjoint B] be positive semidefinite, with tr A=tr B=1. Then (A-B) squared is bounded above by (1-|tr X| squared) times the identity in the Loewner order. All finite dimensions and singular diagonal blocks are included.

For any set of coordinates, sum its two-by-two principal block compressions. The positive semidefinite entry inequality bounds the squared modulus of its X-diagonal sum by the product of the corresponding A and B masses. Apply this to one coordinate and its complement. The triangle inequality gives |tr X| no greater than sqrt(ab)+sqrt((1-a)(1-b)).

The finite total-variation and affinity inequality, applied to the two probability vectors (a,1-a) and (b,1-b), bounds (a-b) squared by one minus the squared affinity. Conjugate all three blocks by the same eigenbasis of A-B. The coordinate bounds then apply to every eigenvalue of that difference, and conjugating back gives the stated squared matrix bound.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.normalized_difference_square_le`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound.normalized_trace_norm_le_one`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../CartesianVariance.md)
- Dependency: [D5/S3/TotalVariation/Bhattacharyya](../../../TotalVariation/Bhattacharyya.md)
