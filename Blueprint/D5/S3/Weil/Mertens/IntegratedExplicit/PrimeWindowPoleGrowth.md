# Growth on every late power window

## Abstract

Zeta zeros and signed Chebyshev tail mass

Let Q(t) be the integral from t to infinity of (ψ(x)−x)/x², where ψ counts prime powers with weight log p at pᵏ. Write B(s,b,Y) for the integral of max(s·(−Q(x)),0)/√x from Y to Yᵇ. For the prime-only tail replace ψ by θ, which counts primes with logarithmic weight. Write A(b,Y) for the resulting integral with s=1.

**Theorem 1.1 (Both signs of the complete tail on every late window).**

$$\forall z \in \mathbb{C},\; \left(\operatorname{zeta}\left(z\right) = 0 \land \frac{1}{2} < \operatorname{Re}\left(z\right)\right) \Rightarrow \left(\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists T \in \mathbb{R},\; \forall Y \in \mathbb{R},\; T \le Y \Rightarrow \left(\forall s \in \mathbb{R},\; \left(s = 1 \lor s = -1\right) \Rightarrow Y^{b(\operatorname{Re}\left(z\right)-\frac{1}{2})-e} \le \operatorname{B}\left(s, b, Y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.off_line_zero_forces_signed_complete_window_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let β be the real part of the given zero. On a vertical line of large real part σ, choose two disks of equal radius. The disk centered at σ is free of zeros. A vertical displacement gives a unique closest zero in the second disk, at distance d less than σ−β+δ. After subtracting the principal part, Cauchy's estimate bounds the analytic remainder. The pole term gives a geometric lower bound for all sufficiently high normalized derivatives. The zero in the second disk can differ from the original zero.

Cauchy's estimate at the real center bounds the absolute value of the real part of the normalized derivative at a smaller geometric rate. The signed moment inequality uses the same derivative lower bound for either sign. Set a=log Y and choose order floor(σha) with 1<h<b. Tilting the two gamma tails controls the parts outside [a,ba]. Inside the window the kernel of order k is bounded by exp(−u/2)/(σ−1/2)ᵏ. Choosing h close to b and δ small gives the stated exponent at every sufficiently large Y.

**Theorem 1.2 (Lower bound for the negative part of the prime-only tail).**

$$\forall z \in \mathbb{C},\; \left(\operatorname{zeta}\left(z\right) = 0 \land \frac{1}{2} < \operatorname{Re}\left(z\right)\right) \Rightarrow \left(\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists T \in \mathbb{R},\; \forall Y \in \mathbb{R},\; T \le Y \Rightarrow Y^{b(\operatorname{Re}\left(z\right)-\frac{1}{2})-e} \le \operatorname{A}\left(b, Y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.off_line_zero_forces_window_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take s=1 in the signed complete window bound. Pointwise comparison of ψ and θ gives B(1,b,Y) ≤ A(b,Y). The difference is at most a multiple of log Y for fixed b.

**Theorem 1.3 (The Riemann hypothesis and arbitrarily late small windows).**

$$\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(RiemannHypothesis \Leftrightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\forall T \in \mathbb{R},\; \exists Y \in \mathbb{R},\; T \le Y \land \operatorname{A}\left(b, Y\right) \le Y^{e}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.rh_iff_frequently_small_prime_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH the complete Mangoldt remainder divided by √x is eventually bounded, so the complete window integral is at most a constant times log Y. The prime-power correction obeys the same upper bound. Conversely, a right-half-strip zero forces a positive power of Y in every sufficiently late window. Choosing a smaller η contradicts the small-window condition. The functional equation carries this exclusion to the other half of the strip.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.off_line_zero_forces_signed_complete_window_mass`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.off_line_zero_forces_window_mass`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.rh_iff_frequently_small_prime_windows`
- Dependency: [D5/S3/Analytic/Laplace/CriticalGammaWindow](../../../Analytic/Laplace/CriticalGammaWindow.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtSignedWindow](CompleteMangoldtSignedWindow.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](PrimeOnlyTailCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
- Dependency: [D5/S3/Weil/ZetaBridge/EqualRadiusZeroDisks](../../ZetaBridge/EqualRadiusZeroDisks.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../ZetaBridge/RightHalfStripRiemannReduction.md)
