# Exceptional indices for two character sums

## Abstract

Simultaneous quadratic Mangoldt tests on a splitting progression

Fix a real loss e > 0 with e/5 ≤ 1/2. At a real height x set u = x^(e/5), N = floor(x^400) and t = x^(1/2+e)/2. For natural q,b,m,A,L take dᵢ = b + m(A+i) for 0 ≤ i < L. Both sums run from n = 1 to N with coefficient Λ(n) min(1,x/n). Their Jacobi factors are (n/dᵢ) and (n/q)(n/dᵢ), respectively.

Write F(e,x,q,b,m,A,L) for the number of indices at which either sum has absolute value strictly greater than t. In the formula, P(e,x,b,m,L) means that b ≡ 3 modulo 4, that 4 divides m, that every prime divisor p of m satisfies p ≤ u or N < p, and that exp(u/2) ≤ 2L.

**Theorem 1.1 (Uniform bound for failure of either test).**

$$\exists U \in \mathbb{R},\; \forall x \in \mathbb{R},\; U \le x \Rightarrow \left(\forall q \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{P}\left(e, x, b, m, L\right) \Rightarrow \operatorname{F}\left(e, x, q, b, m, A, L\right) \le \frac{8 L}{x^{e}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.simultaneous_splitting_progression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the second moment for the retained odd primes coprime to m. The diagonal correlations are at most L. For distinct primes p,r the affine Jacobi correlation cancels on complete blocks of length pr, leaving an absolute error at most L mod pr. Taking absolute values of the cross terms permits the signed coefficients from the extra factor (n/q).

The discarded higher prime powers contribute at most K√x. The prime 2 costs at most log 2, and the discarded odd prime divisors of m cost at most the Chebyshev function θ(u). Since u ≤ √x eventually, the total error is bounded by a constant times √x uniformly in the progression and in q.

For every sufficiently large x the length condition absorbs the remaining polynomial error in each second moment, giving a bound Lx·xᵉ for each sum of squares. An index failing either test contributes at least t² to their combined second moment. Dividing 2Lx·xᵉ by t² gives 8L/xᵉ. The indices represent integer candidates dᵢ. Selecting a prime dᵢ requires a prime-distribution estimate for the varying progression.

## References

- Truth anchor: `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.simultaneous_splitting_progression`
- Dependency: [D5/S3/CharacterSums/DyadicMangoldtPrimeSupply](DyadicMangoldtPrimeSupply.md)
