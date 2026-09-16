# Schulte's gcd-quotient row-sum convolution

## Abstract

Schulte's A350900 row sum is a Dirichlet convolution of two totient sums.

All indices and values are natural numbers, including zero. The symbol n is the row number, i and k are the summation indices from one through n, and d and e are divisors. gcd denotes the greatest common divisor, phi is Euler's totient function, and rowSum(n) is the sum of the entries in row n. The slash denotes natural-number division: the row summands and divisions by divisors are exact quotients. Only the conjectured row-sum convolution is established. The separate statement about arbitrary arithmetic functions is not addressed.

**Definition 1.1 (The A350900 row sum).**

$$\forall n \in \mathbb{N},\; \operatorname{rowSum}\left(n\right) = \sum_{i = 1..n} \sum_{k = 1..n} (\operatorname{gcd}\left(i, n\right)) / (\operatorname{gcd}\left(\operatorname{gcd}\left(i, k\right), n\right))$$

*Formalization.* `D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution.rowSum` (`✓ std3`).

*Citation.* Werner Schulte (2022). *OEIS A350900, T(n,k) = Sum_{i=1..n} gcd(i,n)/gcd(gcd(i,k),n), with the conjectured row sums (n phi(n)) * (Sum_{d|n} d phi(d))*. URL: <https://oeis.org/A350900>.

*Commentary.*

For each n, the outer sum runs over i=1 through n and the inner sum over k=1 through n. Each term is gcd(i,n) divided exactly by gcd(gcd(i,k),n). The sums are empty at n=0.

**Theorem 1.2 (Schulte's row-sum identity).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\operatorname{rowSum}\left(n\right) = \sum_{d \mid n} d \cdot \operatorname{phi}\left(d\right) \cdot \sum_{e \mid (n) / (d)} e \cdot \operatorname{phi}\left(e\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution.result` (`✓ std3`). ∎

*Citation.* Werner Schulte (2022). *OEIS A350900, T(n,k) = Sum_{i=1..n} gcd(i,n)/gcd(gcd(i,k),n), with the conjectured row sums (n phi(n)) * (Sum_{d|n} d phi(d))*. URL: <https://oeis.org/A350900>.

*Commentary.*

For every positive n, the row sum equals the Dirichlet convolution of d times phi(d) with the divisor sum of e times phi(e). Fixing i with g=gcd(i,n), the inner sum over k is (n/g) times the sum of f times phi(f) over divisors f of g; this follows by grouping k by gcd(g,k). The outer sum groups i by g, with phi(n/g) values for each g, and reindexes complementary divisors by d=n/g.

## References

- Truth anchor: `D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution.result`
- Truth anchor: `D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution.rowSum`
