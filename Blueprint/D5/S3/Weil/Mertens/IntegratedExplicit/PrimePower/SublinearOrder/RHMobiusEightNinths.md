# Uniform variation of the exponentially damped degree modes

## Abstract

An eight-ninths exponent for the Möbius prime window

**Theorem 1.1 (The signed prime-window estimate with positive exponent slack).**

$$RH \Rightarrow \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m^{\frac{8}{9} + epsilon} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEightNinths.prime_window_mobius_eight_ninths_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. Write θ(t) for the sum of log p over primes p ≤ t. The tail primeTail(x) is the integral of (θ(t)−t)/t² over t > x. The signed residual E(m,a,B) starts with the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a).

The zero series run over all nontrivial zeta-zero occurrences ρ, with each zero repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)). Both primitives use x > 0.

From E's starting expression subtract P(B)−P(a). For 3 ≤ n ≤ m subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) multiplied by −2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract Pₙ(B)−Pₙ(a) multiplied by −μ(n), where μ is the Möbius function.

Put q=m+1 and u=log x. For each ε>0 choose η=min(ε/2,1/36). The RH ordinary Möbius prefix bound has exponent β=2/3+η. It controls the signed arithmetic tail and the omitted centered response up to u=q. The trivial-root response costs O(q^β(1+log q)).

For u≥q, write vₙ=u/n and E(v)=exp(−u/q+v/2). In the difference of adjacent modes, the phase increment comes with E(vₙ₊₁), so E(vₙ₊₁)(vₙ−vₙ₊₁)≤2(E(vₙ)−E(vₙ₊₁)). The envelope telescopes and bounds the mode variation by O((1+|Im ρ|)/|ρ|) for every u.

The local logarithmic zero count gives an inverse-root bin mass of order (1+|k|)^(η−1). Finite complex Abel summation at low bins costs O(q^β(H+1)^(1+η)). Squaring and summing the high bin masses and applying weighted sampling costs O(qH^(η−1/2)). Balancing the two terms at H=floor(q^(2(1−β)/3)) gives the general window exponent (2+β)/3 with positive slack. With the stated β and remaining slack ε−η/3, the exponent is 8/9+ε.

Integrate the normalized density estimates with the factor exp(−(1/2−1/q)u) between log a and log B. The endpoint gap vanishes for B=a. The constants are uniform in the order and the two endpoints for each fixed ε.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEightNinths.prime_window_mobius_eight_ninths_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerPrefixWindow](PowerPrefixWindow.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusEnergyPointwise](../../../../ZetaPntBounds/MobiusEnergyPointwise.md)
