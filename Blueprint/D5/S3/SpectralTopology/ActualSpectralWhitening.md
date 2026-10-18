# Smooth actual spectral functions at constant PSD rank

## Abstract

Smooth actual spectral functions at constant PSD rank

The result concerns the actual functional-calculus support, inverse square root with value zero on the kernel, and nonnegative square root of a smooth positive semidefinite matrix family whose rank is constant. The manifold, matrix size and rank are arbitrary; compactness, nonempty base and positive rank are not required. A global eigenbasis and smoothness of the spectral functions are not supplied as inputs.

The Hermitian square map has the existing derivative V mapped to YV+VY and is smooth. At a positive definite Y, the existing Traces.jordan_conjugation and Traces.diagonal_conjugated_jordan give positive coefficients lambda(i)+lambda(j), so this derivative is a continuous linear equivalence. The inverse function theorem supplies a smooth local inverse. The identities sqrt(X squared)=X on a positive definite neighborhood and square(sqrt(A))=A identify that local inverse with the actual CFC square root. Continuity of the square root is not assumed in this identification.

For a constant-rank PSD family, selected independent columns C of Q give a local Gram projection C(C* C) inverse C*. Equality of symmetric projections on the actual Euclidean range identifies this projection with spectralSupport Q. This gives smoothness of the specified support. With P that support, H=Q+1-P is positive definite. Functional calculus gives W=P(sqrt(H)) inverse and sqrt(Q)=P sqrt(H). Smooth inversion and the positive definite root result then prove the entire spectral triple.

The statement allows moving ranges. For example, a positive scalar times the projection onto the rotating unit vector (cos(t),sin(t)) is a rank-one family in dimension two; the range varies although its rank is constant. The zero family is also in scope with rank zero. These examples explain applicability and do not add instance theorems or numerical certificates.

The proof reuses HermitianCubeDerivative.square_hasFDerivAt and square_contDiff, ProjectionRange smooth matrix operations and the existing local Gram certificate. The imported cube-root theorem is a different matrix function; this result proves smoothness of the specified square root. This is a classical analytic construction, with no claim of literature novelty.

The six public targets have unfinished four-slot escape audits tracked at https://github.com/the-omega-institute/trureturing/issues/18787. No compiled registration or declared_validated status is asserted. The actual input-first Choi rank, full tensor atlas application, global Theta and inverse, sigma and W squared restrictions, decoder, root-column family and Stinespring realization remain separate original ST37 obligations. This analytic endpoint does not settle original8340 or its parent atoms.

**Remark 1.1 (Herm).**

Lean statement: `D5/S3/SpectralTopology/ActualSpectralWhitening.Herm`

*Formalization.* `D5/S3/SpectralTopology/ActualSpectralWhitening.Herm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Herm n is the real self-adjoint submodule of complex Fin n square matrices, with the inherited norm and real linear structure.

**Theorem 1.2 (positive_hermitian_sqrt_contDiffAt).**

$$\forall q\in PositiveHermitianData, SmoothHermitianRoot\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_hermitian_sqrt_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PositiveHermitianData is the complete original input: an arbitrary natural n, A in the real self-adjoint submodule of complex Fin n square matrices, and a proof that A.val is positive definite. SmoothHermitianRoot means ContDiffAt over R of smooth order top, at A, of X mapped to CFC.sqrt(X.val), valued in the ambient matrix space.

**Theorem 1.3 (support_range).**

$$\forall q\in PSDMatrixData, ActualSupportRange\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.support_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PSDMatrixData consists of arbitrary n, a complex Fin n square matrix Q and its positive-semidefiniteness proof. ActualSupportRange means the conjunction: the Euclidean linear ranges of spectralSupport Q and Q agree; spectralSupport Q is Hermitian; and spectralSupport Q squared equals itself.

**Theorem 1.4 (actual_constant_rank_support_smooth).**

$$\forall q\in ConstantRankPSDData, SmoothSupport\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_support_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ConstantRankPSDData contains all original quantified inputs: arbitrary types E,H,B, a real normed additive model E, topologies on H and B, a charted-space structure, I a real model with corners, an IsManifold I infinity B instance, arbitrary natural n and r, Q from B to complex Fin n square matrices, ContMDiff I of smooth order infinity of Q, positive semidefiniteness at every point, and matrix rank Q(x)=r at every point. SmoothSupport means ContMDiff I of smooth order infinity of x mapped to spectralSupport(Q(x)), in the same ambient matrix space.

**Theorem 1.5 (positive_matrix_sqrt_smooth).**

$$\forall q\in PositiveFamilyData, SmoothRoot\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_matrix_sqrt_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PositiveFamilyData contains arbitrary E,H,B, the same real manifold structures and smoothness order as ConstantRankPSDData, arbitrary natural n, a smooth ambient matrix family Q, and positive definiteness of every Q(x). It assumes no constant rank separately. SmoothRoot means ContMDiff I of smooth order infinity of x mapped to the actual CFC.sqrt(Q(x)).

**Theorem 1.6 (actual_whitening_extension).**

$$\forall q\in PSDMatrixData, ExtensionIdentities\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_whitening_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q in PSDMatrixData, define P=spectralSupport Q and H=Q+1-P. ExtensionIdentities is exactly H.PosDef and spectralInverseSqrt Q=P*(CFC.sqrt H) inverse and CFC.sqrt Q=P*CFC.sqrt H, where inverse is the matrix inverse. These values include the kernel of Q.

**Theorem 1.7 (actual_constant_rank_whitening_smooth).**

$$\forall q\in ConstantRankPSDData, SmoothSpectralTriple\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_whitening_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q in ConstantRankPSDData, SmoothSpectralTriple is exactly the conjunction of real ContMDiff I, smooth order infinity, of spectralSupport composed with Q, spectralInverseSqrt composed with Q, and CFC.sqrt composed with Q, all valued in the ambient complex matrix space. No additional premises are packaged into this predicate.

## References

- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.Herm`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_support_smooth`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_whitening_smooth`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_whitening_extension`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_hermitian_sqrt_contDiffAt`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_matrix_sqrt_smooth`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.support_range`
- Dependency: [D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative](../Geometry/AlphaGeometry/HermitianCubeDerivative.md)
- Dependency: [D5/S3/Geometry/ProjectionRange/Prebundle](../Geometry/ProjectionRange/Prebundle.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../Quantum/Recovery/SpectralTransposeRecovery.md)
