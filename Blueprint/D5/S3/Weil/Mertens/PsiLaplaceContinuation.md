# PsiLaplaceContinuation

## Abstract

Measurability of the actual psi source

**Theorem 1.1 (Measurability of the actual psi source).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

qpsi(u)=exp(-u)*(psi(exp u)-exp u), with the actual Chebyshev psi function.

**Theorem 1.2 (Unconditional source integrability).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing WeightedPrimeLimit.chebyshev_error_kernel_integrable is transported by x=exp u, including the Jacobian. Boundedness alone is not an L1 argument.

**Theorem 1.3 (Entire oriented finite correction).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Apsi_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Apsi_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite correction Apsi(U,s)=integral_(0..U) exp(-su)*qpsi(u) is entire for every real U, in both orientations, by the existing finiteHead_entire theorem.

**Theorem 1.4 (Actual positive-half-plane continuation identity).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Qpsi_eq_Mpsi`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Qpsi_eq_Mpsi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real cutoff U and Re s>0, the actual integral Qpsi(U,s) equals -(1+logDeriv(zeta1,1+s))/(1+s)-Apsi(U,s). The Mellin identity uses actual von Mangoldt coefficients, Mathlib SumCoeff and the existing Mangoldt prefix estimate. There is no prime-power correction.

**Theorem 1.5 (Regularity of the full real corridor).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Mpsi_real_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Mpsi_real_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized-zeta expression Mpsi is analytic at every real x>-1, including zero. It uses the existing normalized zeta nonvanishing result on the positive real axis; it makes no assertion of integral convergence there.

**Theorem 1.6 (Complete local source pole).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.actual_source_poles`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceContinuation.actual_source_poles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nontrivial zeta zero rho in the open critical strip, a=rho-1 lies in Re s>-1, is nonzero and nonreal. With m the full positive analytic multiplicity and Lambda=-m/rho, Mpsi=Lambda/(s-a)+H on a full punctured complex neighborhood, where H is analytic. The source order is -1 and the order of -Mpsi prime+Mpsi is -2. Real analyticity excludes real source poles. No condition at 2*rho or simple-zero assumption is used.

**Theorem 1.7 (Full complex source coefficient).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.source_normalized_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceContinuation.source_normalized_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by s-a in the source pole expansion tends to Lambda=-m/rho in the full complex punctured neighborhood. This supplier is consumed by the forcing coefficient theorem.

## References

- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Apsi_entire`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Mpsi_real_analytic`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.Qpsi_eq_Mpsi`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.actual_source_poles`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_integrable`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_measurable`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceContinuation.source_normalized_limit`
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](../../Analytic/Laplace/EulerPoleObstruction.md)
- Dependency: [D5/S3/Weil/Mertens/CriticalThetaTailPeak](CriticalThetaTailPeak.md)
- Dependency: [D5/S3/Weil/Mertens/ThetaLaplaceContinuation](ThetaLaplaceContinuation.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](WeightedPrimeLimit.md)
