# A rate from the actual separation of the degree samples

## Abstract

A power-saving rate for the Möbius prime window

**Theorem 1.1 (Power saving in the truncation order).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m^{\frac{27}{28}} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusPower.prime_window_mobius_power_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. Write θ(t) for the sum of log p over primes p ≤ t. The tail primeTail(x) is the integral of (θ(t)−t)/t² over t > x. The signed residual E(m,a,B) starts with the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a).

The zero series run over all nontrivial zeta-zero occurrences ρ, with each zero repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)). Both primitives use x > 0.

From E's starting expression subtract P(B)−P(a). For 3 ≤ n ≤ m subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) multiplied by −2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract Pₙ(B)−Pₙ(a) multiplied by −μ(n), where μ is the Möbius function.

Put q=m+1 and u=log x. The zero-free half-plane estimate with θ=1/2 and α=1/4 gives the ordinary Möbius prefix bound of order q^(3/4). For u≤q, use that bound with signed Abel summation on the omitted degrees. The exponential factor exp(u/p) is at most exp(2), where p=ceil(q/2).

For q≤u≤q^(29/28), split the occurrence sum at the unit-bin height H=floor(q^(1/7)). Below the cutoff, finite complex Abel summation costs the prefix bound times the total variation of the normalized mode. Its variation is bounded by a constant times (1+|Im ρ|u/q)/|ρ|. The total inverse-root mass below the cutoff is of order (H+1)^(1/4).

Above the cutoff the squared bin masses sum to at most a constant times H^(−1/2). The separation of the actual degree samples bounds that contribution by a constant times q H^(−1/4). Both contributions have order at most q^(27/28). For u≥q^(29/28), the uncut separated sampling bound costs 1+q²/u+q^(7/8).

The signed trivial-root response costs q^(3/4)(1+log q). On the arithmetic tail the interval Möbius prefix at q+j is bounded by a constant times q^(−1/4)(q+j). Abel summation with the decreasing Chebyshev weights gives a normalized tail of order q^(3/4).

Extract exp(−(1/2−1/q)u) from the density estimates and integrate between log a and log B. The resulting endpoint power difference includes coincident endpoints. One threshold and one constant work for every m≥2.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusPower.prime_window_mobius_power_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerWindowDensity](PowerWindowDensity.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusInverseLog](RHMobiusInverseLog.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/SignedOmittedSpectrum](SignedOmittedSpectrum.md)
