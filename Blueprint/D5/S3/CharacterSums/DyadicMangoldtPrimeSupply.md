# The quadratic Mangoldt sum on dyadic prime bands

## Abstract

Square-root cancellation for auxiliary primes on arbitrarily high dyadic scales

Fix ε > 0. In block k put X = 2ᵏ, x = (k log 2)^(5/ε) and N = floor(x^400). For primes q congruent to 3 modulo 8 in [X/2,X), form the real sum from n = 1 to N of Λ(n) min(1,x/n) times the Jacobi symbol (n/q). B(ε,k) and G(ε,k) sum (log q)/q over primes whose absolute sum respectively exceeds or is at most x^(1/2+ε)/2. At k = 0 the implementation uses [1,2), of zero weight. In the formula, summableBad(e) means that the block weights B(e,k) have a convergent series, and accepted(e,K) sums G(e,k) from k = 1 through K.

**Theorem 1.1 (Finite exceptional weight and divergent accepted weight).**

$$\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\operatorname{summableBad}\left(e\right) \land \left(\forall M \in \mathbb{R},\; \exists S \in \mathbb{N},\; \forall K \in \mathbb{N},\; S \le K \Rightarrow M \le \operatorname{accepted}\left(e, K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DyadicMangoldtPrimeSupply.dyadic_quadratic_mangoldt_supply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Represent the clipping factor by integrating x/t² for t greater than both x and n. The nonprime contribution is controlled by the Chebyshev bound ψ(t) − θ(t) ≤ C√t. Integration costs at most 2C√x, uniformly in the cutoff N.

For the remaining odd prime terms expand the square and average over all integers congruent to 3 modulo 8 in the band. Distinct primes p,r have zero complete correlation and an incomplete-period error at most 8pr. The diagonal costs at most the band length times the sum of the squared coefficients. The harmonic bound controls this sum by x(log N)²(1+log N).

The band length grows exponentially in x^(ε/5). It absorbs the polynomial endpoint error. Restrict to prime denominators by positivity and bound exceptions using the square of the threshold. Eventually the bad weight per block is at most 4/((log 2)⁴ k⁴). The complete residue class has divergent logarithmic prime weight. Subtract the finite exceptional total and telescope the disjoint blocks.

This supplies arbitrarily high dyadic scales. In the modulus-one comparison the approximation by the logarithmic derivative, its zero exclusions, and the choice of the second prime require further estimates.

## References

- Truth anchor: `D5/S3/CharacterSums/DyadicMangoldtPrimeSupply.dyadic_quadratic_mangoldt_supply`
- Dependency: [D5/S3/CharacterSums/QuadraticPrimeCrossPeriod](QuadraticPrimeCrossPeriod.md)
