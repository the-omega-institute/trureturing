# A positive first radial moment bounds the physical reflection gap

## Abstract

An integrated separation reserve for the complete physical theta kernel.

Write Phi=romikPhi, p=(a+b)/2, d=|a-b|/2, r0=p^2+d^2, and I_v,p(r)=cosh(2*v*sqrt(r-p^2))*Phi(sqrt(r-p^2)+p)*Phi(sqrt(r-p^2)-p). The full theta series and the entire unbounded integration domain are retained.

**Definition 1.1 (The reflected first excess moment).**

Lean statement: `D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap.reflectedRadialMoment`

*Formalization.* `D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap.reflectedRadialMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reflected radial moment is the integral over r>r0 of (r-r0)*I_v,p(r). The definition imposes no truncation. Its positivity and genuine integrability under positive a,b and arbitrary real v are established along the proof of the next theorem.

**Theorem 1.2 (The curvature reserve survives complete integration).**

Lean statement: `D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap.physical_kernel_integrated_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap.physical_kernel_integrated_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b>0 and every real v, the reflected radial moment is strictly positive, and a*b/24 times that moment is strictly less than physicalKernel(v,a,b)-physicalKernel(v,a,-b).

The prior pointwise bound makes the nonnegative correction C(r)=a*b*(r-r0)*I_v,p(r)/6 smaller than the integrable difference I_v,d(r)-I_v,p(r) almost everywhere. Domination proves C and the first excess moment integrable. The remaining difference is positive on an interval of positive measure. The existing exact radial substitutions supply the factor 1/4, hence the constant 1/24. Evenness of cosh removes the nonnegative-weight restriction of the source pointwise estimate.

The exceptional radial point r=2*p^2 is removed only as a Lebesgue null singleton. No pointwise claim is made there. This is an actual integrated bound with an explicit moment on its left side; no numerical estimate for that moment is asserted. The theorem compares individual kernel entries and does not establish matrix positive semidefiniteness or RH. Literature novelty is not claimed.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap.physical_kernel_integrated_gap`
- Truth anchor: `D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap.reflectedRadialMoment`
- Dependency: [D5/S3/Weil/ZetaGamma/ThetaReflectedKernelComparison](ThetaReflectedKernelComparison.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap](ThetaReflectedQuantitativeGap.md)
