# Complex qubit mixed cubic compatibility

## Abstract

The original ordered trace coefficients and a positive six-row mixed cubic certificate.

**Theorem 1.1 (Trace product of positive matrices).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_mul_nonneg_of_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_mul_nonneg_of_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite matrices over an RCLike field, the real trace of a product of two PSD matrices is nonnegative. This shared spectral proof also supplies the weighted trace Gram theorem.

**Definition 1.2 (Hermitian coordinates).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two by two matrix with real diagonal a,b and upper off-diagonal z; the lower off-diagonal is the complex conjugate of z.

**Theorem 1.3 (Hermitian coordinate construction).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate matrix is Hermitian for every pair of real diagonal entries and every complex off-diagonal entry.

**Theorem 1.4 (All Hermitian qubit matrices).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complex Hermitian two by two matrix equals the coordinate matrix formed from its two real diagonal entries and its upper entry.

**Definition 1.5 (A symmetric two point kernel).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.weightedImage`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.weightedImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,b,m, weightedImage multiplies K00 by a, K11 by b, and both off-diagonal entries by m.

**Theorem 1.6 (The kernel in Hermitian coordinates).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.weightedImage_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.weightedImage_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel action sends the Hermitian coordinates r,s,z to ar,bs,mz, for arbitrary real a,b,m.

**Theorem 1.7 (The joint endpoint estimate).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.endpoint_coupling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.endpoint_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative a,b, let X-H with diagonal a-h,b-k and upper entry -z and I+K with diagonal 1+r,1+s and upper entry w both be PSD. Then |z|+sqrt(ab)|w| is at most sqrt((a-h+a(1+r))(b-k+b(1+s))). The PSD determinant bounds and the two term Cauchy inequality retain the original coupling; no inverse or strict endpoint is needed.

**Theorem 1.8 (The contraction row estimate).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.contraction_row`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.contraction_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex Hermitian two by two K with both I+K and I-K PSD, the squared modulus of K01 is at most 1-K00^2. Both determinant constraints are used, and singular endpoints are allowed.

**Theorem 1.9 (The actual displacement entry).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.displacement_coupling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.displacement_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If m>=sqrt(ab), the same coupled endpoints give |z-mw|<=sqrt((2a-(h-ar))(2b-(k-bs)))+(m-sqrt(ab))|w|. The argument uses the complex triangle inequality and the joint endpoint estimate, with arbitrary complex phases.

**Theorem 1.10 (The weighted row estimate).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.displacement_row`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.displacement_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0, h<=a and the two contraction endpoints of K, |K01|^2<=2(2a-(h-aK00))/a. This also covers K01=0.

**Theorem 1.11 (Exact weighted quadratic trace).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_weighted_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_weighted_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the diagonal matrix X=diag(a,b) and Hermitian L with diagonal u,v and upper entry z, Re Tr(XL^2)=a(u^2+|z|^2)+b(v^2+|z|^2). All variables are arbitrary, and no positivity is assumed.

**Theorem 1.12 (The complete qubit pure cubic estimate).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coupled_cubic_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coupled_cubic_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a,b>0 and complex Hermitian two by two H,K, assume X+H,X-H,I+K,I-K are PSD, where X=diag(a,b). Put m=2(a^2+ab+b^2)/(3(a+b)), M=weightedImage(a,b,m,K), L=H-M and B=(a-b)^2(a^2+3ab+b^2)|K01|^2/(3(a+b)). Then |Re Tr(L^3)|<=2 Re Tr(XL^2)+2B/3. There is no trace restriction, no restriction on the complex off-diagonal phases, and no assumption that an endpoint is invertible. The exact coupled scalar estimate applies after a simultaneous sign reversal and a coordinate exchange when required.

**Definition 1.13 (The original second trace coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.traceCoefficient2`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.traceCoefficient2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary square complex matrices indexed by a finite type, this is the ordered trace-word polynomial p2 at alpha=3 and Y=I. It is defined directly from the word table, independently of the positive certificate.

**Definition 1.14 (The original third trace coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.traceCoefficient3`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.traceCoefficient3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third ordered trace-word polynomial p3 uses the original factor orders. No commutation of X,H,K or inverse endpoint premise is added.

**Definition 1.15 (The real second coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient2`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real part of traceCoefficient2. Its identification with one half of the physical second derivative is a separate analytic obligation.

**Definition 1.16 (The real third coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient3`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real part of traceCoefficient3. Its identification with one sixth of the physical third derivative is a separate analytic obligation.

**Theorem 1.17 (The second matrix trace jet).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_jet_coefficient2`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_jet_coefficient2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In arbitrary finite dimension, set L=H-(2/3)XK and M=-(4/3)HK+(10/9)XK^2. Then Tr(3MXX+6LLX)=2p2. The exact identity uses trace cyclicity, with no Hermitian premise.

**Theorem 1.18 (The third matrix trace jet).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_jet_coefficient3`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_jet_coefficient3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same L,M and N=(10/3)HK^2-(80/27)XK^3, Tr(3NXX+9MLX+9MXL+6LLL)=6p3 in arbitrary finite dimension. Every ordered word is retained until trace cyclicity is applied. The actual function derivative supplier consumes this identity.

**Definition 1.19 (The first row coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.f`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real rational weight 2(a+2b)/(3(a+b)) in the first Gram row.

**Definition 1.20 (The cubic correction in the first row).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.q`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real rational weight -(a-b)(3a^2+9ab+8b^2)/(18(a+b)^2).

**Definition 1.21 (The second Gram weight).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.c`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight (a-b)^2(2a+3b)/(a+b)^2, nonnegative at positive a,b.

**Definition 1.22 (The second row correction).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.j`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.j` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real rational weight b^2/(3(a+b)) in the second Gram row.

**Definition 1.23 (The third Gram weight).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.d`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight (a-b)^2(a+2b)(7a^2+14ab+4b^2)/(36(a+b)^2).

**Definition 1.24 (A complex row Gram matrix).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.rowGram`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.rowGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two by two positive form R*R of rank at most one associated with R=(x,y).

**Definition 1.25 (Six weighted row-Gram forms).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixedMatrix`

*Formalization.* `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixedMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary real diagonal displacement entries and complex upper entries w,z, mixedMatrix is a sum of six row-Gram matrices of rank at most one. Its rational coefficients have denominators that are powers of a+b; the definition therefore does not divide by the spectral gap a-b.

**Theorem 1.26 (Positivity of the mixed certificate).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixedMatrix_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixedMatrix_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a,b>0 and arbitrary displacement entries, the six-row certificate is positive semidefinite. No endpoint premise on H is needed.

**Theorem 1.27 (The second coefficient energy identity).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coordinate_energy_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coordinate_energy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X=diag(a,b), L have Hermitian coordinates u,v,w, K have coordinates r,s,z, and H=L+weightedImage(a,b,m,K), where m=2(a^2+ab+b^2)/(3(a+b)). If a+b is nonzero, then p2=3 Re Tr(XL^2)+B, where B=(a-b)^2(a^2+3ab+b^2)|z|^2/(3(a+b)). The identity is derived by ordered matrix multiplication.

**Theorem 1.28 (The coordinate mixed bound).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coordinate_mixed_cubic_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coordinate_mixed_cubic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b>0 and I+K,I-K positive semidefinite, arbitrary complex Hermitian L and H=L+weightedImage(a,b,m,K) satisfy |3 Re Tr(L^3)-3p3|<=3p2. The exact identities 3 Tr(L^3)-3p3=Tr(KN) and Tr(N)=3p2, together with N>=0, supply both signs of the bound.

**Theorem 1.29 (The mixed bound for arbitrary Hermitian inputs).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixed_cubic_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixed_cubic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b>0 and arbitrary complex Hermitian two by two H,K, if I+K and I-K are positive semidefinite, then with L=H-weightedImage(a,b,m,K), |3 Re Tr(L^3)-3p3|<=3p2. There is no endpoint restriction on H in this theorem.

**Theorem 1.30 (The energy identity without coordinates).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.energy_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.energy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex Hermitian H,K and a+b nonzero, the original real coefficient p2 equals 3 Re Tr(XL^2)+B, with the same weighted displacement and B as in the coordinate identity.

**Theorem 1.31 (Full qubit coefficient compatibility).**

Lean statement: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b>0, X=diag(a,b), and arbitrary complex Hermitian two by two H,K, assume X+H,X-H,I+K,I-K are positive semidefinite. Then p2>=0 and 3|p3|<=5p2. This combines the six-row mixed certificate with the coupled pure cubic estimate. Spectral levels may coincide and endpoints may be singular; complex phases are unrestricted.

The source is a supplier for the alpha=3, Y=I, complex two dimensional restriction of the He-Saunderson-Fawzi compatibility question, arXiv:2502.05627v1 Conjecture 6.2 and published Conjecture 1, DOI 10.1007/s10107-025-02314-0. Identification with derivatives of the matrix power function is not asserted here. The unrestricted HSF conjecture and literature priority remain unclaimed.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.c`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient2`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient3`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coefficient_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.contraction_row`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coordinate_energy_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coordinate_mixed_cubic_bound`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.coupled_cubic_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.d`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.displacement_coupling`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.displacement_row`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.endpoint_coupling`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.energy_identity`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.f`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian_eq`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.hermitian_isHermitian`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.j`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixedMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixedMatrix_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.mixed_cubic_bound`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.q`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.rowGram`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.traceCoefficient2`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.traceCoefficient3`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_jet_coefficient2`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_jet_coefficient3`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_mul_nonneg_of_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.trace_weighted_square`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.weightedImage`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfQubitMixedCubic.weightedImage_hermitian`
- Dependency: [D5/S3/Quantum/Matrix/HsfQubitCoupledScalar](HsfQubitCoupledScalar.md)
