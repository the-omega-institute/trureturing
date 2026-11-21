# Exceptional indices for two character sums

## Abstract

Simultaneous quadratic Mangoldt tests on a splitting progression

For x > 0, real y and t, and a natural cutoff N, write w(n) = Λ(n) min(1,x/n). Let v be any real multiplier with |v(n)| ≤ 1. Assume every prime divisor p of the natural stride m satisfies p ≤ y or N < p. Let P be the odd primes up to N coprime to m and set a(p) = log(p) min(1,x/p) v(p). For a natural denominator d let F(d) be the full sum of w(n)v(n)(n/d) for 1 ≤ n ≤ N and G(d) the sum of a(p)(p/d) over P.

**Theorem 1.1 (Uniform discarded mass).**

$$\operatorname{abs}\left(\operatorname{F}\left(d\right)-\operatorname{G}\left(d\right)\right) \le E$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.clipped_coprime_prime_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists an absolute K ≥ 0 such that E = K√x + log 2 + θ(y) works for every choice above and every d. The three terms bound higher prime powers, the prime 2, and the discarded odd prime divisors of m.

For the finite moment bound assume b ≡ 3 modulo 4 and 4 divides m. Take arbitrary natural A and L, and write Fᵢ = F(b+m(A+i)) for 0 ≤ i < L. Let B be the sum over all ordered p,r in P. Its diagonal summands are L a(p)². For p ≠ r, with h = L mod (pr), the summand is |a(p)a(r)| min(h,pr−h). Write S = Σᵢ Fᵢ² and M = (√B + E√L)². Set H = Σᵢ max(0,|Fᵢ|−E)² and let J be the count of i with t < |Fᵢ| multiplied by max(0,t−E)².

**Theorem 1.2 (Finite moment and threshold bounds at any cutoff).**

$$S \le M \land \left(H \le B \land J \le B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.finite_clipped_progression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An absolute K ≥ 0 works uniformly in all these parameters. The excess over E is at most the absolute retained prime sum. Expanding its square gives the diagonal bound L and the off-diagonal correlations. A full block of pr terms sums to zero. Removing full periods bounds the remainder by h, while completing the final block bounds it by pr−h. Cauchy–Schwarz gives the full second moment from the excess, and threshold counting gives the last inequality. Both also cover an empty interval.

Fix a real loss e > 0. At a real height x set u = x^(e/5), N = floor(x^400) and t = x^(1/2+e)/2. For natural q,b,m,A,L take dᵢ = b + m(A+i) for 0 ≤ i < L. Both sums run from n = 1 to N with coefficient Λ(n) min(1,x/n). Their Jacobi factors are (n/dᵢ) and (n/q)(n/dᵢ), respectively. Mathlib defines (n/q) by multiplying over all prime factors of q with multiplicity, with empty product 1 at q = 0 or 1.

Write F(e,x,q,b,m,A,L) for the number of indices at which either sum has absolute value strictly greater than t. In the formula, P(e,x,b,m,L) means that b ≡ 3 modulo 4, that 4 divides m, that every prime divisor p of m satisfies p ≤ u or N < p, and that exp(u/2) ≤ 2L.

**Theorem 1.3 (Uniform bound for failure of either test).**

$$\exists U \in \mathbb{R},\; \forall x \in \mathbb{R},\; U \le x \Rightarrow \left(\forall q \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{P}\left(e, x, b, m, L\right) \Rightarrow \operatorname{F}\left(e, x, q, b, m, A, L\right) \le \frac{8 L}{x^{e}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.simultaneous_splitting_progression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the second moment for the retained odd primes coprime to m. The diagonal correlations are at most L. For distinct primes p,r the affine Jacobi correlation cancels on complete blocks of length pr, leaving an absolute error at most L mod pr. Taking absolute values of the cross terms permits the signed coefficients from the extra factor (n/q).

The discarded higher prime powers contribute at most K√x. The prime 2 costs at most log 2, and the discarded odd prime divisors of m cost at most the Chebyshev function θ(u). For x ≥ 1, both √x and u are at most x^(1/2+e/4). Thus the squared error per index is bounded by a constant times x·x^(e/2), uniformly in q and in the progression.

For every sufficiently large x the length condition absorbs the remaining polynomial error in each second moment, giving a bound Lx·xᵉ for each sum of squares. An index failing either test contributes at least t² to their combined second moment. Dividing 2Lx·xᵉ by t² gives 8L/xᵉ. The indices represent integer candidates dᵢ. Selecting a prime dᵢ requires a prime-distribution estimate for the varying progression.

## References

- Truth anchor: `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.clipped_coprime_prime_error`
- Truth anchor: `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.finite_clipped_progression`
- Truth anchor: `D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.simultaneous_splitting_progression`
- Dependency: [D5/S3/CharacterSums/AffineJacobiCorrelation](AffineJacobiCorrelation.md)
- Dependency: [D5/S3/CharacterSums/DyadicMangoldtPrimeSupply](DyadicMangoldtPrimeSupply.md)
