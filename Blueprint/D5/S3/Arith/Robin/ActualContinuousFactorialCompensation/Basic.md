# Actual Continuous Factorial Compensation

## Abstract

The literal factorial and complete von Mangoldt dilation sum admits continuous compensation, exact finite smoothing and an identified almost-everywhere derivative with global logarithmic bounds.

Here gamma is Euler's constant, L=log(2*pi), and eta is the existing actual factorial error log(floor(x)!)-x*log(x)+x. The function B retains every von Mangoldt term for 2<=n<=floor(x), weighted by 1-fract(x/n), and subtracts gamma*x. Set h=eta-L-B, h1=1+gamma-L, Z_h(x)=sum over 1<=k<=floor(x) of h(x/k), ceta=integral over y>1 of eta(y)/y^2, alpha=gamma^2+2*ceta-2, and G(x)=Z_h(x)-h1*floor(x)-alpha*(x-1). These are literal arithmetic objects; no supplier identity or regularity is a theorem hypothesis. The public G_formula is the exact arithmetic supplier consumed by SignedLaplace; it is not reproved there.

**Theorem 1.1 (The literal harmonic prefix).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.H_harmonic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.H_harmonic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x, H(x) is harmonic(floor(x)), cast to the reals. This normalization is consumed by the real-floor harmonic bound and by the cancellation proof.

**Theorem 1.2 (Integrability of the actual epsilon density).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.epsilonDensity_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.epsilonDensity_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual epsilonDensity(t)=epsilon(t)/t is integrable on the complete set t>1. The original Basic proof bounds its absolute value by the integrable inverse-square density; Basic uses it for the actual improper tail.

**Theorem 1.3 (Exact finite smoothing at every real cutoff).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.finite_smoothing`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.finite_smoothing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, Z_h(x)=x*((1+gamma-log(x))*H(x)+2*J(x)) -log(floor(x)!)-L*floor(x), where H and J are the right-closed harmonic and logarithmic harmonic prefixes. The finite divisor triangle retains every product endpoint and all prime powers. This identity is consumed by the compensation construction as arithmetic normalization.

**Theorem 1.4 (The literal G is the slope primitive).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.G_eq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.G_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, G(x)=integral from 1 to x of slope(t). The slope is (gamma-log(x))*H(x)+2*J(x)-alpha. Abel summation pays the floor jumps in this exact identity. This exposed existing seam is consumed by the causal owner's exponential change of variables; it is not a separate claim of novel arithmetic cancellation.

**Theorem 1.5 (Measurability of the actual arithmetic slope).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.slope_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.slope_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual slope is measurable by the measurable floor prefixes and log. This existing seam supplies the causal slope and lifted slope measurability proofs, with no assumption about a substitute function.

**Theorem 1.6 (Complete compensation and actual restricted-ae derivative).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.compensation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.compensation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full contract states G(1)=0, ContinuousOn G on [1,infinity), and absolute continuity on every [1,X] with X>=1. For every x>=1, abs(G(x))<=(gamma+2)*log(x)+log(x)^2/2; for every t>=0, abs(G(exp(t)))<=(gamma+2)*t+t^2/2. For every x>=1, slope(x) equals (gamma+log(x))*epsilon(x)+2*T_epsilon(x), where epsilon=H-log-gamma and T_epsilon is the full integral over u>x of epsilon(u)/u; abs(slope(x))<=(gamma+2+log(x))/x.

In the same public contract, for almost every x with respect to volume restricted to [1,infinity), HasDerivAt G (slope(x)) x and abs(deriv G x)<=(gamma+2+log(x))/x. Interval-integrable FTC on [1,n+2], a countable intersection, and local equality with the literal G identify its actual derivative. The endpoint one is a null singleton; ordinary differentiability at every integer cutoff is not asserted.

The live construction proves ceta-1=-integral over u>1 of epsilon(u)/u by comparing the factorial and harmonic Abel identities and their improper limits. This cancels the literal alpha constant in slope. The exact primitive representation then supplies continuity, absolute continuity, growth and the derivative identification. No finite tail truncation or supplied centering constant replaces these proofs.

The factorial and envelope suppliers remain at ActualFactorialRobinHighDerivative and LogConvolutionMassExpansion, preserving the latter owner's Terence Tao / Apache-2.0 attribution. Harmonic, divisor, Abel and integral APIs come from Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 with Lean 4.35.0. This is a repository-derived source construction with no literature novelty claim. It establishes no signed-inverse RH cancellation, complete quadratic positivity or sufficient moment order N(D)=o(D).

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.G_eq_integral`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.H_harmonic`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.compensation`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.epsilonDensity_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.finite_smoothing`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic.slope_measurable`
- Dependency: [D5/S3/Arith/Robin/ActualFactorialRobinHighDerivative](../ActualFactorialRobinHighDerivative.md)
- Dependency: [D5/S3/Weil/Mertens/Estimates](../../../Weil/Mertens/Estimates.md)
