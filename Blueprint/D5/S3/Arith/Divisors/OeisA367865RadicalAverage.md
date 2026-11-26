# OEIS A367865 Radical Average

## Abstract

The radical-weighted divisor sum is the radical average over a complete positive interval.

**Theorem 1.1 (The exact identity for every positive n).**

$$\forall n\in \mathbb{N}, 1\le n \Rightarrow \sum_{d\in\operatorname{Nat}.\operatorname{divisors}\left(n\right)} d \cdot \phi(d) \cdot \mu(d)^{2} = \frac{rad\left(n\right)}{n} \cdot \sum_{k\in\operatorname{Finset}.\operatorname{Icc}\left(1, n\right)} \frac{rad\left(n \cdot k\right)}{rad\left(k\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA367865RadicalAverage.result` (`✓ std3`). ∎

*Citation.* OEIS Foundation Inc. (2026). *OEIS A367865*. URL: <https://oeis.org/A367865>.

*Commentary.*

For every positive natural n, the equality is interpreted in ℚ. The divisor sum uses positive Nat.divisors and the average uses Finset.Icc 1 n, so n = 1 remains in the statement.

Set m = rad(n). The prime-factor product identity gives rad(nk) gcd(m,k) = m rad(k), hence the quotient is m/gcd(m,k). This function has period m. Grouping one period by gcd gives the totient-weighted divisor sum, and m divides n supplies complete periods.

The squarefree radical m has exactly the squarefree divisors of n. Mathlib's Möbius square identity therefore turns the left side into the same totient-weighted divisor sum. The proof is the direct rational composition of these identities.

## References

- Truth anchor: `D5/S3/Arith/Divisors/OeisA367865RadicalAverage.result`
