# Growth on every late power window

## Abstract

Zeta zeros and the negative part of the prime tail

Let Q(t) be the integral from t to infinity of (θ(x)−x)/x², where θ counts each prime with logarithmic weight. Write A(b,Y) for the integral of max(−Q(x),0)/√x from Y to Yᵇ. The prime powers of exponent at least two change the corresponding complete Mangoldt budget by at most a multiple of log Y.

**Theorem 1.1 (Lower bound from a zero to the right of the critical line).**

$$\forall z \in \mathbb{C},\; \left(\operatorname{zeta}\left(z\right) = 0 \land \frac{1}{2} < \operatorname{Re}\left(z\right)\right) \Rightarrow \left(\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists T \in \mathbb{R},\; \forall Y \in \mathbb{R},\; T \le Y \Rightarrow Y^{b(\operatorname{Re}\left(z\right)-\frac{1}{2})-e} \le \operatorname{A}\left(b, Y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.off_line_zero_forces_window_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let β be the real part of the given zero. On a vertical line of large real part σ, choose two disks of equal radius. The disk centered at σ is free of zeros. A vertical displacement gives a unique closest zero in the second disk, at distance d less than σ−β+δ. After subtracting the principal part, Cauchy's estimate bounds the analytic remainder. The pole term gives a geometric lower bound for all sufficiently high normalized derivatives. The zero in the second disk can differ from the original zero.

Adding the derivative at the real center bounds this quantity by twice the positive Mangoldt moment. Set a=log Y and choose order floor(σha) with 1<h<b. Tilting the two gamma tails controls the parts outside [a,ba]. Inside the window the kernel of order k is bounded by exp(−u/2)/(σ−1/2)ᵏ. Choosing h close to b and δ small gives the stated exponent at every sufficiently large Y.

**Theorem 1.2 (The Riemann hypothesis and arbitrarily late small windows).**

$$\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(RiemannHypothesis \Leftrightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\forall T \in \mathbb{R},\; \exists Y \in \mathbb{R},\; T \le Y \land \operatorname{A}\left(b, Y\right) \le Y^{e}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.rh_iff_frequently_small_prime_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH the complete Mangoldt remainder divided by √x is eventually bounded, so the complete window integral is at most a constant times log Y. The prime-power correction obeys the same upper bound. Conversely, a right-half-strip zero forces a positive power of Y in every sufficiently late window. Choosing a smaller η contradicts the small-window condition. The functional equation carries this exclusion to the other half of the strip.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.off_line_zero_forces_window_mass`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.rh_iff_frequently_small_prime_windows`
- Dependency: [D5/S3/Analytic/Laplace/CriticalGammaWindow](../../../Analytic/Laplace/CriticalGammaWindow.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne](CompleteMangoldtAtOne.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtMoments](CompleteMangoldtMoments.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](PrimeOnlyTailCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
- Dependency: [D5/S3/Weil/ZetaBridge/EqualRadiusZeroDisks](../../ZetaBridge/EqualRadiusZeroDisks.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../ZetaBridge/RightHalfStripRiemannReduction.md)
