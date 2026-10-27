# Quantitative reflected theta-integrand gaps

## Abstract

Explicit pointwise separation of complete reflected theta integrands.

Write Phi=romikPhi, P_c(r)=Phi(sqrt(r-c^2)+c)*Phi(sqrt(r-c^2)-c), and I_v,c(r)=cosh(2*v*sqrt(r-c^2))*P_c(r). These are the existing radialProduct and radialIntegrand of ThetaReflectedKernelComparison, with the full theta series retained.

**Theorem 1.1 (A quantitative gap between radial integrands).**

Lean statement: `D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap.radial_integrand_gap_quantitative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap.radial_integrand_gap_quantitative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real v,c,q,r with v>=0, 0<=c<q, r>q^2+c^2 and r!=2*q^2, one has I_v,q(r)*(1+(q^2-c^2)*(r-q^2-c^2)/6)<I_v,c(r). Every hypothesis, including the exceptional radial point, is retained.

Apply the strict symmetric-pair inequality to h(z)+z^2/48, where h(z)=log(Phi(sqrt(z))). Exact algebra converts the squared spread difference into the displayed positive correction. Exponentiation and 1+t<=exp(t) give the product gap, and positivity and monotonicity of cosh preserve its strict direction.

**Theorem 1.2 (The gap in the physical reflection parameters).**

Lean statement: `D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap.physical_kernel_gap_quantitative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap.physical_kernel_gap_quantitative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b>0 and v>=0, put p=(a+b)/2, d=|a-b|/2 and r0=p^2+d^2. Whenever r>r0 and r!=2*p^2, I_v,p(r)*(1+a*b*(r-r0)/6)<I_v,d(r). The exact identity p^2-d^2=a*b supplies this form of the radial bound.

Despite its theorem name, this conclusion is a pointwise radial-integrand inequality. It does not assert an integrated numerical lower bound for the physical kernel gap. The integrated strict comparison is supplied separately by ThetaReflectedKernelComparison. These results do not establish positive definiteness of finite Gram matrices or all-support Weil positivity, and imply no unconditional RH result. This is a repository derivation; literature novelty is not asserted.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap.physical_kernel_gap_quantitative`
- Truth anchor: `D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap.radial_integrand_gap_quantitative`
- Dependency: [D5/S3/Analytic/Fourier/ThetaQuantitativeCurvature](../../Analytic/Fourier/ThetaQuantitativeCurvature.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ThetaReflectedKernelComparison](ThetaReflectedKernelComparison.md)
