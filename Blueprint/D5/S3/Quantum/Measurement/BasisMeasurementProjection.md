# Basis-Measurement Projection

## Abstract

Basis measurement is the orthogonal projection onto diagonal Hermitian operators, including on the trace-zero carrier.

**Lemma 1.1 (A basis projector retains its underlying matrix).**

$$\forall B, j, \operatorname{val}\left(\operatorname{basisProjector}\left(B, j\right)\right) = \operatorname{projector}\left(B, j\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basisProjector_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A basis projector is the context projector equipped with its Hermitian certificate. Forgetting that certificate returns the original projector matrix exactly, so the real Hermitian-space carrier does not alter the operator.

**Lemma 1.2 (Basis measurement is unread measurement on matrices).**

$$\forall B, A, \operatorname{val}\left(\operatorname{basisMeasurement}\left(B, A\right)\right) = \operatorname{unreadState}\left(\operatorname{projector}\left(B\right), \operatorname{val}\left(A\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basisMeasurement_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-linear basis-measurement operator is the unread measurement channel restricted to Hermitian matrices. On underlying matrices, its value is precisely the sum of the basis compressions, with no additional normalization or projection step.

**Lemma 1.3 (Complete basis measurement preserves trace).**

$$\forall B, A, \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \Rightarrow \operatorname{Tr}\left(\operatorname{val}\left(\operatorname{basisMeasurement}\left(B, A\right)\right)\right) = \operatorname{Tr}\left(\operatorname{val}\left(A\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basis_measurement_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complete projective record measurement, the diagonal-block sum has the same trace as the input Hermitian matrix. Consequently the basis-measurement restriction preserves the affine trace slices, in particular the trace-zero subspace.

**Lemma 1.4 (The range is exactly the diagonal Hermitian subspace).**

$$\forall B, \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \Rightarrow \operatorname{range}\left(\operatorname{basisMeasurement}\left(B\right)\right) = \operatorname{diagonalSubspace}\left(B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basis_measurement_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every measured Hermitian operator is a real linear combination of the context's rank-one projectors, so the image lies in their span. Conversely, each basis projector is fixed by the measurement, which makes every generator, and hence the entire diagonal span, belong to the image.

**Theorem 1.5 (Basis measurement is the diagonal orthogonal projection).**

$$\begin{gathered}\forall d, B: \operatorname{RankOneContext}\left(d\right), \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \Rightarrow\\{}\operatorname{IsSymmetricProjection}\left(\operatorname{basisMeasurement}\left(B\right)\right) \land\\{}\operatorname{range}\left(\operatorname{basisMeasurement}\left(B\right)\right) = \operatorname{diagonalSubspace}\left(B\right) \land\\{}(\forall A, D: \operatorname{HermitianSpace}\left(d\right), D \in \operatorname{diagonalSubspace}\left(B\right) \Rightarrow \operatorname{innerR}\left(A - \operatorname{basisMeasurement}\left(B, A\right), D\right) = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basis_measurement_is_orthogonal_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complete rank-one basis measurement is idempotent and symmetric for the real Hilbert--Schmidt inner product. Together with the exact range calculation, this identifies the measurement with the orthogonal projection onto the diagonal Hermitian subspace.

For every Hermitian input, the discarded off-diagonal component is orthogonal to every diagonal Hermitian operator. Thus the theorem records both the projection operator and its defining residual orthogonality, rather than only idempotence or range containment.

**Lemma 1.6 (The trace-zero restriction projects onto trace-zero diagonals).**

$$\forall d, B: \operatorname{RankOneContext}\left(d\right), \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \Rightarrow\\{}\operatorname{IsSymmetricProjection}\left(\operatorname{traceZeroBasisMeasurement}\left(B\right)\right) \land\\{}\operatorname{range}\left(\operatorname{traceZeroBasisMeasurement}\left(B\right)\right) = \operatorname{diagonalTraceZeroSubspace}\left(B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BasisMeasurementProjection.trace_zero_basis_measurement_is_orthogonal_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace preservation makes the trace-zero Hermitian carrier invariant under basis measurement. The restricted real-linear operator remains idempotent and symmetric, so it is an orthogonal projection.

Its range is exactly the diagonal operators whose trace is zero. The reverse inclusion uses trace preservation to choose a trace-zero preimage, ruling out the weaker conclusion of mere containment in the diagonal trace-zero subspace.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basisMeasurement_val`
- Truth anchor: `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basisProjector_val`
- Truth anchor: `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basis_measurement_is_orthogonal_projection`
- Truth anchor: `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basis_measurement_range`
- Truth anchor: `D5/S3/Quantum/Measurement/BasisMeasurementProjection.basis_measurement_trace`
- Truth anchor: `D5/S3/Quantum/Measurement/BasisMeasurementProjection.trace_zero_basis_measurement_is_orthogonal_projection`
- Dependency: [D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection](../../Observer/Conditioning/UnreadStateOrthogonalProjection.md)
- Dependency: [D5/S3/Quantum/Tomography/RankOneContextCommutator](../Tomography/RankOneContextCommutator.md)
