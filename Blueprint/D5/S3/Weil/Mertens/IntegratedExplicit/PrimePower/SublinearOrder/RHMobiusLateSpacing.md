# Keep the spacing of the high-frequency samples

## Abstract

A smaller exponent on late signed RH prime windows

**Theorem 1.1 (The signed prime-window bound with a logarithmic starting point).**

$$RH \Rightarrow \left(\forall d \in \mathbb{R},\; \left(0 \le d \land d \le \frac{1}{2}\right) \Rightarrow \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(\left(T \le a \land a \le B\right) \land \left(m + 1\right)^{1 + d} \le \operatorname{log}\left(a\right)\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m^{\frac{3}{4} - \frac{d}{2} + epsilon} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusLateSpacing.prime_window_mobius_late_spacing_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. The window discrepancy is the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a). The tail primeTail(x) integrates (θ(t)−t)/t² over t>x, where θ(t) sums log p over primes p≤t.

The zero series use all actual nontrivial zero occurrences, each repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)), for x>0.

The signed residual E(m,a,B) subtracts P(B)−P(a) from the window discrepancy and then subtracts both signed correction sums. For 3≤n≤m, the first sum uses −2 μ(n)n²/((n−1)(n−2)) multiplied by a^(1/n−1/2)−B^(1/n−1/2). For 2≤n≤m and 2n<m+1, the second sum uses −μ(n) multiplied by Pₙ(B)−Pₙ(a).

Write q=m+1 and u=log x. Inside the integration interval u≥q^(1+d). With η=min(ε/3,1/12), the ordinary Möbius prefix controls the arithmetic and trivial-root terms. The low-frequency estimate uses the signed degree prefix with cutoff H.

The high-frequency bound retains the sampling distance u/q². The derivative of each phase is controlled by the square mass of the bin envelope min(q,1+|k|)(1+|k|)^(η−1). The total high-frequency cost is bounded by a constant times the sum [(1+q²/u)H^(η−1/2)+q^(1/2+η)].

Take H=floor(q^(1/2−d)), including H=1 at d=1/2. The low and high estimates then both have order at most q^(3/4−d/2+2η). Integrating between log a and log B gives the original endpoint gap, including value zero at equality.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusLateSpacing.prime_window_mobius_late_spacing_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/LateWindowSpectrum](LateWindowSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedPrefixSpectrum](OmittedPrefixSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerWindowDensity](PowerWindowDensity.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusShortAverage](../../../../ZetaPntBounds/MobiusShortAverage.md)
