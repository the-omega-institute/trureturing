# SpectralTransposeRecovery

## Abstract

The existing finite-matrix functional calculus constructs a support projection and spectral inverse square root. The shared decoder normalization lemma is the existing proof extracted once and consumed by both the original candidate and the reference completion; it claims no independent mathematical gain. Explicit Kraus completion gives a canonical CPTP candidate even for a zero CP branch. Exact recoverability and smoothness are separate conclusions.

**Theorem 1.1 (spectral support on kraus).**

Lean statement: `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_support_on_kraus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_support_on_kraus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and E. Knill (2002). *Reversing quantum dynamics with near-optimal quantum and classical fidelity*. DOI: [10.1063/1.1459754](https://doi.org/10.1063/1.1459754).

*Commentary.*

The existing finite-matrix functional calculus constructs a support projection and spectral inverse square root. The shared decoder normalization lemma is the existing proof extracted once and consumed by both the original candidate and the reference completion; it claims no independent mathematical gain. Explicit Kraus completion gives a canonical CPTP candidate even for a zero CP branch. Exact recoverability and smoothness are separate conclusions.

**Theorem 1.2 (spectral decoder normalization).**

Lean statement: `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_decoder_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_decoder_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and E. Knill (2002). *Reversing quantum dynamics with near-optimal quantum and classical fidelity*. DOI: [10.1063/1.1459754](https://doi.org/10.1063/1.1459754).

*Commentary.*

The existing finite-matrix functional calculus constructs a support projection and spectral inverse square root. The shared decoder normalization lemma is the existing proof extracted once and consumed by both the original candidate and the reference completion; it claims no independent mathematical gain. Explicit Kraus completion gives a canonical CPTP candidate even for a zero CP branch. Exact recoverability and smoothness are separate conclusions.

**Theorem 1.3 (spectral transpose candidate).**

Lean statement: `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_transpose_candidate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_transpose_candidate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and E. Knill (2002). *Reversing quantum dynamics with near-optimal quantum and classical fidelity*. DOI: [10.1063/1.1459754](https://doi.org/10.1063/1.1459754).

*Commentary.*

The existing finite-matrix functional calculus constructs a support projection and spectral inverse square root. The shared decoder normalization lemma is the existing proof extracted once and consumed by both the original candidate and the reference completion; it claims no independent mathematical gain. Explicit Kraus completion gives a canonical CPTP candidate even for a zero CP branch. Exact recoverability and smoothness are separate conclusions.

## Smooth support and inverse square root for channel families

Let B be a possibly empty compact smooth real manifold, with a model with corners I on an arbitrary finite-dimensional real normed space E and its chart model H. Let d and n be positive natural numbers, let k be a natural number, and let N_x: M_d(C) → M_n(C) be a smooth family of the canonical FiniteStateChannel.QuantumChannel maps. Here smooth means ContMDiff of order infinity after restricting each channel's linear map to R and regarding it as a continuous linear map between CStarMatrix spaces. Suppose that for every x there exists a CPTP map R_x with R_x(N_x(X)) = X for every complex d-by-d matrix X, and that rank(Q_x) = k d for Q_x = N_x(I_d). The recovery maps are pointwise witnesses; no smooth choice of R_x is assumed.

Under these hypotheses, the actual canonical maps P_x = spectralSupport(Q_x) and W_x = spectralInverseSqrt(Q_x) are globally smooth as matrix-valued maps on B. The parameter correspondence is the input index Fin d, output index Fin n, real manifold model I, and local column index Fin r with r = rank(Q_x) = k d. The CStarMatrix.ofMatrix equivalence identifies the channel value N_x(I_d) with Q_x in Matrix (Fin n) (Fin n) C. For positive semidefinite Q, spectralSupport is the orthogonal projection onto range(Q), obtained from the scalar function that is zero at zero and one elsewhere. spectralInverseSqrt applies the scalar function t ↦ (sqrt(t))⁻¹; it is zero on ker(Q) and equals Q⁻¹/² on range(Q).

Evaluation of the smooth continuous-linear-map family N at the fixed identity is smooth, and the fixed real continuous linear matrix equivalence preserves smoothness. Thus Q is smooth. Complete positivity of the actual FiniteStateChannel channel sends the positive identity to a positive element; transport through CStarMatrix.ofMatrixStarAlgEquiv and Matrix.nonneg_iff_posSemidef gives positive semidefiniteness of Q_x. These are derived properties of N, rather than additional assumptions on a replacement matrix family. Constant rank k d supplies the locally constant rank needed below.

Fix x in B and choose r linearly independent actual columns of Q_x spanning its range. Keep their indices J: Fin r → Fin n fixed, and write C_y(i,j) = Q_y(i,J(j)). The Gram matrix G_x = C_x† C_x is positive definite and invertible. Continuity of its determinant keeps G_y invertible on an open neighborhood of x. Intersect this neighborhood with one on which rank(Q_y) = r. On this same neighborhood the selected columns remain independent, lie in range(Q_y), and span it because both dimensions are r. Consequently P_y = C_y (C_y† C_y)⁻¹ C_y† there. Indeed this expression is the self-adjoint projection onto range(C_y) = range(Q_y), hence the canonical spectral support. The existing spectral_support_on_kraus identity gives the compatible support action on PSD factors and their column images; the local columns here come from Q itself and require no smooth Kraus choice.

Column selection, matrix multiplication and the adjoint are smooth over R, and matrix inversion is smooth on the open set of units. For the latter, the fixed CStarMatrix equivalence transports the existing contDiffAt_ringInverse result to the ordinary matrix inverse near an invertible matrix. Therefore the local Gram formula proves smoothness of the actual P at x. Since every x admits such a neighborhood, P is globally smooth.

Set A_x = Q_x + I_n - P_x. The PSD spectral decomposition shows that A_x acts by each positive eigenvalue of Q_x on its range and by one on its kernel. Thus A_x is positive definite; since Q and P are smooth, so is A. The positive square root is taken in the real vector space of Hermitian matrices, namely selfAdjoint.submodule R (Matrix (Fin n) (Fin n) C). The real continuous linear self-adjoint-part map gives a smooth lift of A to this subspace, with the same matrix value.

To see the square root's regularity, fix a positive definite Hermitian A and put Y = sqrt(A). The existing HermitianCubeDerivative.square_hasFDerivAt and square_contDiff give smoothness of the square map and its derivative V ↦ YV + VY. HermitianCubeDerivative.Traces.jordan_conjugation and diagonal_conjugated_jordan express this derivative in real Hermitian coordinates with coefficients lambda_i + lambda_j. All these coefficients are positive because Y is positive definite, so the derivative is injective and, in finite dimension, a continuous linear equivalence. The pinned Mathlib inverse function theorem applies. On the open positive definite neighborhood of Y, CFC.sqrt_sq identifies the actual square root as a left inverse of the square map, while CFC.sq_sqrt gives Y² = A. HasStrictFDerivAt.localInverse_unique identifies this root with the local inverse, and ContDiffAt.to_localInverse gives its smoothness. The eigenbasis is used at this fixed point only; the argument assumes neither a smooth eigenbasis nor prior continuity of the root, and asserts no ambient complex square-root regularity.

Since sqrt(A_x) is positive definite, inversion on units and smooth matrix multiplication now give smoothness of P_x (sqrt(A_x))⁻¹. On a positive eigenvalue t of Q_x this product has value 1/sqrt(t); on the zero eigenspace it has value zero. Finite spectral functional calculus therefore identifies it with the actual W_x = spectralInverseSqrt(Q_x). Equivalently W_x = P_x sqrt(A_x⁻¹). Local choices of columns and local inverses agree on overlaps because they equal these same canonical P and W. Their smoothness glues on B without a global smooth frame or a global eigenbasis.

The empty manifold is included, since smoothness is local at each point. The local Gram argument also permits r = 0: Fin 0 gives the empty Gram matrix, invertible in the zero-dimensional matrix algebra. For a rank-zero PSD family Q = 0 one has P = W = 0 and A = I; in the original positive-dimensional CPTP setting on a nonempty B, trace(Q_x) = d > 0 excludes this case. At full rank P = I and A = Q. Repeated positive eigenvalues cause no singularity, since the Jordan coefficients are sums of positive eigenvalues.

The hypotheses doing the work for P and W are smoothness of the actual Q, its positive semidefiniteness, finite matrix size and locally constant rank. Compactness and pointwise exact recoverability remain part of the original channel setting but are unused in this P/W derivation; no uniform spectral gap or chosen recovery family is needed for this conclusion. A change of rank falls outside the argument. The transpose/Petz candidate above retains its Barnum–Knill attribution. Its CPTP normalization does not establish that this candidate is an exact left inverse. The remaining original claims concerning pi, the decoder, F, Theta and sigma, the Choi construction in ST37.2 and the Chern obstruction in ST38 are separate obligations; P/W smoothness alone does not establish global bundle recovery or close those claims.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_decoder_normalization`
- Truth anchor: `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_support_on_kraus`
- Truth anchor: `D5/S3/Quantum/Recovery/SpectralTransposeRecovery.spectral_transpose_candidate`
- Dependency: [D5/S3/Quantum/Recovery/KrausCompletion](KrausCompletion.md)
