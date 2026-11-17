# Smooth-circle Fourier products and finite contact expansion

## Abstract

Smooth-circle Fourier products and finite contact expansion

Mathlib supplies completion, normed operators, Fourier analysis, integer binomial identities and unconditional sum machinery under Apache 2.0. The additional arguments here concern the stated original objects and relations. No literature novelty or physical realization is asserted.

**Theorem 1.1 (Fourier multipliers of differential binomials).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.coefficient_frequencyBinomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.coefficient_frequencyBinomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Test is the existing globally smooth complex function of period 2*pi. Define D=-i*d/dtheta and P_0 f=f, P_(j+1) f=(D-j)P_j f/(j+1). For every natural j and integer m, the mth coefficient of P_j f equals choose(m,j)*fhat(m). Periodicity and the fundamental theorem of calculus handle the zero frequency before any division by m.

**Theorem 1.2 (Differential contact vanishes for a zero product).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.frequencyBinomial_product_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.frequencyBinomial_product_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If f(theta)*g(theta)=0 for every real theta, then (P_j f)(theta)*g(theta)=0 for every natural j and real theta. At a point where g is nonzero, continuity supplies a neighborhood where f vanishes, and every derivative of f vanishes there.

**Theorem 1.3 (Closed quotient-circle support separation).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.product_zero_of_disjoint_tsupport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.product_zero_of_disjoint_tsupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disjoint closed supports of the actual periodic lifts on AddCircle(2*pi) imply f(theta)*g(theta)=0 for all real theta. The supports are defined on the quotient circle, including the seam.

**Theorem 1.4 (Fourier coefficient of a pointwise product).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.fourierCoeff_mul_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.fourierCoeff_mul_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For continuous complex F,G on AddCircle(T), T>0, absolute summability of the Fourier coefficients of F implies that sum over all integer m of Fhat(m)*Ghat(t-m) has sum the tth coefficient of the pointwise product F*G, and the scalar series is absolutely summable. Uniform Fourier reconstruction is followed by the bounded linear coefficient functional of multiplication by G.

**Theorem 1.5 (Absolute double smearing).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_absolute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_absolute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any complete complex normed space and C:Z->Z->E satisfy norm C(m,n)<=K*(1+abs(m))^R*(1+abs(n))^R with K>=0 and natural R. Every pair of genuine Tests f,g gives an absolutely norm-summable series fhat(m)*ghat(n) acting on C(m,n) over Z x Z, bounded termwise by the product of the two existing weighted Fourier majorants.

**Theorem 1.6 (Absolute contact rows).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.contact_series_absolute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.contact_series_absolute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original C, bound K,R and every natural j, the series over t in Z of the norm of the coefficient of (P_j f)*g at t acting on c_j(t) is summable. This follows from the absolute double majorant after the bijection (t,m)->(m,t-m), before evaluating any iterated sum.

**Theorem 1.7 (Finite Banach-valued contact formula).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.delta_smooth_contact_formula`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.delta_smooth_contact_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complete complex normed E, natural R,N, K>=0 and C with the stated polynomial bound and delta^N C=0, the double smear equals sum over j<N and all integer t of coefficient(((P_j f)*g),t) acting on c_j(t). The conclusion includes absolute convergence of the original double series and every contact series. Newton reconstruction is followed only by rearrangements justified by absolute summability. At N=0 the contact sum is empty.

**Theorem 1.8 (Vanishing of a double smear).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_product_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_product_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses on E,C,K,R,N, if the genuine tests have pointwise zero product, the full double smear is zero. Each differential contact product vanishes, so every term of the finite contact expansion is zero.

**Theorem 1.9 (Separated smooth supports annihilate finite contact).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_disjoint_tsupport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_disjoint_tsupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those same Banach-space growth and delta hypotheses, disjoint closed supports of the actual quotient-circle lifts imply the full all-integer double smear is zero. This statement concerns the original coefficients and genuine smooth tests; no commutation conclusion is an input.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.coefficient_frequencyBinomial`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.contact_series_absolute`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.delta_smooth_contact_formula`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_absolute`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_disjoint_tsupport`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_product_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.fourierCoeff_mul_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.frequencyBinomial_product_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.product_zero_of_disjoint_tsupport`
- Dependency: [D5/S3/VertexAlgebra/Analysis/IntegerNewton](IntegerNewton.md)
- Dependency: [D5/S3/VertexAlgebra/Analysis/SmoothCircleFourier](SmoothCircleFourier.md)
