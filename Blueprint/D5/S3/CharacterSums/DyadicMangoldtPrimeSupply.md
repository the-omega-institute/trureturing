# The quadratic Mangoldt sum on prime bands

## Abstract

Square-root cancellation for auxiliary primes on dyadic blocks and real scales

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

**Theorem 1.2 (The first prime at each sufficiently large real scale).**

$$\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists S \in \mathbb{R},\; \forall x \in \mathbb{R},\; S \le x \Rightarrow \left(\forall E \in F,\; \operatorname{card}\left(E\right) \le \operatorname{B}\left(e, x\right) \Rightarrow \operatorname{L}\left(e, x\right) \le \operatorname{Mass}\left(e, x, E\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DyadicMangoldtPrimeSupply.real_scale_quadratic_mangoldt_supply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ε > 0 set T = x^(ε/5). Consider the primes q congruent to 3 modulo 8 in (exp(T/2), exp(T)]. Keep q outside a finite set E if the actual sum with cutoff floor(x^400) has absolute value at most x^(1/2+ε)/2. Mass(ε,x,E) is the sum of (log q)/q over these primes. In the formula B(ε,x) = exp(T/3), L(ε,x) = T/173065984000, and F is the set of finite subsets of the natural numbers.

The progression window estimate gives total prime weight at least T/86532992000. Cover the band with at most 3T dyadic integer blocks. In every block touching the band, its left endpoint A satisfies 2A ≥ exp(T/2). Keep x and the cutoff fixed throughout. The complete second moment bounds the combined exceptional weight by 36T²/x^ε, which is o(T).

Each excluded prime has weight at most T exp(−T/2), so at most exp(T/3) further exclusions cost at most T exp(−T/6). For each fixed ε > 0 the latter loss and the character-sum exceptions each consume at most one quarter of the total lower bound for all sufficiently large x. Applying this to exceptional conductors requires a separate bound on their number.

## References

- Truth anchor: `D5/S3/CharacterSums/DyadicMangoldtPrimeSupply.dyadic_quadratic_mangoldt_supply`
- Truth anchor: `D5/S3/CharacterSums/DyadicMangoldtPrimeSupply.real_scale_quadratic_mangoldt_supply`
- Dependency: [D5/S3/CharacterSums/PrimeProgressionWindowMass](PrimeProgressionWindowMass.md)
- Dependency: [D5/S3/CharacterSums/QuadraticPrimeCrossPeriod](QuadraticPrimeCrossPeriod.md)
