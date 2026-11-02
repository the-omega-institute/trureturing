# Geometric mean lower bound

## Abstract

The matrix geometric mean dominates a quantitative arithmetic correction.

**Definition 1.1 (Geometric mean).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean`

*Formalization.* `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For finite complex square matrices P and Q, set geometricMean(P,Q) to the existing inverse-base mean gmInv(P inverse,Q). For positive definite inputs this is P^(1/2)(P^(-1/2) Q P^(-1/2))^(1/2)P^(1/2). The total definition also assigns zero whenever either input is zero; these are the singular cases needed by the block inequality.

**Theorem 1.2 (Positive Riccati solution).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_riccati`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_riccati` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every dimension and positive definite P,Q, their geometric mean G is positive definite and satisfies G P inverse G=Q. This uses the existing AlternativeMeanLinearization.riccati theorem at base P inverse and supplies positivity and the identity used below.

Application: covariance metrics. The following is an ordinary application derivation of existing formal facts, not additional exported Lean declarations. Write X* for conjugate transpose, Re Tr for the real part of the trace, and X≥0 for positive semidefiniteness. All products below retain their displayed order; no commutativity or common spectral basis is assumed.

Rectangular square. Let m,k be arbitrary finite index types, D an m×m complex positive definite matrix, and A,C arbitrary m×k complex matrices. D inverse is the ordinary two-sided inverse and is Hermitian. With E=A−D inverse C, the ordered expansion is E* D E = A* D A − A* D (D inverse C) − (D inverse C)* D A + (D inverse C)* D (D inverse C) = A* D A + C* D inverse C − A* C − C* A. Here D(D inverse C)=C and (D inverse C)*D=C*. Matrix.PosSemidef.conjTranspose_mul_mul_same applied to D and E makes this k×k remainder positive semidefinite.

Sharp rectangular trace bound. Matrix.PosSemidef.trace_nonneg and RCLike.nonneg_iff give a nonnegative real trace of that remainder. Matrix.trace_conjTranspose gives Re Tr(C* A)=Re Tr(A* C), so 2 Re Tr(A* C)≤Re Tr(A* D A)+Re Tr(C* D inverse C). The coefficient 2 is attained by D=I and A=C≠0 whenever the dimensions allow a nonzero factor. This is a bound on the real cross trace; no absolute-value or Schatten estimate is asserted.

Ordered Riccati square. For any n≥0, positive definite complex n×n D and Hermitian n×n G, put K=(D−G)D inverse(D−G). Expansion in the given order gives K=D D inverse D−D D inverse G−G D inverse D+G D inverse G=D−G−G+G D inverse G. Thus D+G D inverse G−G−G=K≥0, by congruence of the positive matrix D inverse with the Hermitian matrix D−G. Positivity of G is not needed for this square identity.

Weighted trace positivity. For positive definite n×n P and positive semidefinite n×n K, set H=CFC.sqrt(P). The existing CFC.sqrt_mul_sqrt_self gives H H=P, and the positive square root is Hermitian. Congruence makes H K H=H* K H positive semidefinite. Matrix.trace_mul_comm and associativity give Tr(KP)=Tr(K H H)=Tr(H K H), hence Re Tr(KP)≥0 by trace_nonneg. This argument does not require or assert that the product KP is Hermitian or positive semidefinite.

Optimizer orientation. Let P,S be positive definite complex n×n matrices and set G=geometricMean(P inverse,S). Applying geometricMean_riccati to P inverse and S, then cancelling the double inverse of P, gives G positive definite and G P G=S. The first argument is P inverse. Equivalently, G=P^(-1/2)(P^(1/2) S P^(1/2))^(1/2)P^(-1/2): the positive matrix P^(1/2) G P^(1/2) squares to P^(1/2) S P^(1/2), which identifies its positive square root.

Exact cost gap. For every positive definite n×n competitor D define J(D)=Re Tr(DP)+Re Tr(D inverse S). Cyclicity gives Tr((G D inverse G)P)=Tr(D inverse(G P G))=Tr(D inverse S). Multiply D+G D inverse G−G−G=K by P and take the real trace to obtain J(D)−2 Re Tr(GP)=Re Tr(((D−G)D inverse(D−G))P)≥0. Weighted trace positivity applies to this K and the same actual P; no independently chosen covariance or spectrum is substituted.

Attainment. Since G is positive definite and G P G=S, cancellation gives G inverse S=P G. Therefore J(G)=Re Tr(GP)+Re Tr(PG)=2 Re Tr(GP). Together with the gap this proves J(G)≤J(D) for every positive definite D, and min over positive definite D of J(D)=2 Re Tr(GP). This is the attained global value on the stated positive definite domain; no separate equality characterization or uniqueness assertion is made here.

Rectangular correspondence and limits. Taking P=A A* and S=C C* uses rectangular trace cyclicity to rewrite the right side of the rectangular bound as J(D). The optimizer calculation applies to these covariances only if both A A* and C C* are positive definite. In applications C=ZB, with B an r×k matrix and Z an m×r matrix, the same statement uses the actual product ZB. The rectangular square and bound allow arbitrary rank-deficient and zero A,C, since only D is inverted. They include m=0, k=0 and n=0, where the corresponding traces and identities vanish. No inverse or attained optimizer for arbitrary singular metrics or singular covariances follows from this derivation.

Scope and attribution. The reused suppliers are geometricMean and geometricMean_riccati in this module, AlternativeMeanLinearization.riccati, Matrix.PosSemidef.conjTranspose_mul_mul_same, Matrix.PosSemidef.trace_nonneg, Matrix.trace_mul_comm, Matrix.trace_conjTranspose, CFC.sqrt_mul_sqrt_self and the positive-square-root Hermitian facts. These yield the displayed application through inverse cancellation, ordered expansion and trace normalization. The derivation is not a new kernel theorem or a literature novelty claim, does not solve Audenaert's norm-compression conjecture, and supplies no joint Schatten comparison for unrelated spectra.

**Theorem 1.3 (Harmonic lower bound).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_le_geometricMean`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_le_geometricMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every positive definite P,Q, the inverse of (P inverse+Q inverse)/2 is at most their geometric mean G in Loewner order. The Riccati equation gives G inverse P G inverse=Q inverse. The positive quadratic form (G inverse−P inverse) P (G inverse−P inverse) equals P inverse+Q inverse−2G inverse. Inverse order then gives the asserted comparison without a commutation assumption.

**Theorem 1.4 (Exact arithmetic correction).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_eq_arithmetic_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_eq_arithmetic_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For H=(P+Q)/2 and K=(P−Q)/2 with P,Q positive definite, the harmonic mean is exactly H−K H inverse K. The intermediate expression P H inverse Q has inverse Q inverse H P inverse=(P inverse+Q inverse)/2. Expanding P=H+K and Q=H−K preserves the order of all matrix factors.

**Theorem 1.5 (Quantitative lower bound).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.arithmetic_sub_le_geometricMean`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.arithmetic_sub_le_geometricMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every dimension, positive definite P,Q and real c,d with c>0, put H=(P+Q)/2 and K=(P−Q)/2. If cI≤H and K²≤dI, then H−(d/c)I≤geometricMean(P,Q). Inverse order yields H inverse≤I/c; conjugation by Hermitian K and the square bound give K H inverse K≤(d/c)I. The exact harmonic correction and harmonic lower bound complete the argument. Taking d to be the squared operator norm of K recovers the corresponding operator norm estimate.

**Theorem 1.6 (Independent positive scaling).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every positive definite P,Q and positive real r,s, geometricMean(rP,sQ)=sqrt(rs) geometricMean(P,Q). The scaled matrix is positive definite and satisfies the scaled Riccati equation, so uniqueness identifies the two means. This identity restores arbitrary diagonal traces after normalization.

**Theorem 1.7 (Zero second input).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every complex square matrix P, geometricMean(P,0)=0. This includes every dimension and supplies the zero-block branch.

**Theorem 1.8 (Zero first input).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every complex square matrix Q, geometricMean(0,Q)=0. This includes every dimension and supplies the other zero-block branch.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.arithmetic_sub_le_geometricMean`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_riccati`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_smul`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_left`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_right`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_eq_arithmetic_correction`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_le_geometricMean`
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](../AlternativeMeanLinearization.md)
- Dependency: [D5/S3/Quantum/Matrix/CayleyResolvent](../CayleyResolvent.md)
