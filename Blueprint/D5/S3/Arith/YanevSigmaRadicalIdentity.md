# Yanev's Sigma-Radical Identity

## Abstract

Yanev's identity expresses every positive divisor-power sum through ordinary divisor sums and the radical.

All variables take values in the natural numbers N. The named operator primeRadical is the frozen primeRadical of D5/S1/Deficit/AlmostAdditivity (A007947), the product of the distinct prime divisors, with empty product one. The notation sigma(k,x) denotes the sum of the k-th powers of the positive divisors of x, and is zero at x = 0. Powers, products and inequalities are in N, and m - 1 is truncated natural subtraction.

**Theorem 1.1 (The general divisor-power identity).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, (0 < n) \implies (0 < m) \implies \operatorname{sigma}\left(m, n\right) \cdot \operatorname{sigma}\left(1, \operatorname{primeRadical}\left(n\right)^{(m - 1)}\right) = \operatorname{sigma}\left(1, n^{m} \cdot \operatorname{primeRadical}\left(n\right)^{(m - 1)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/YanevSigmaRadicalIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a023887-yanev-sigma-radical-identity` (proved) by `D5/S3/Arith/YanevSigmaRadicalIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a023887-yanev-sigma-radical-identity","declaration_gid":"D5/S3/Arith/YanevSigmaRadicalIdentity.result","resolution_kind":"proved"} -->

*Citation.* Olivier Gérard; Velin Yanev (2017). *OEIS A023887, sigma_n(n), with Yanev's sigma_m identity*. URL: <https://oeis.org/A023887>.

*Commentary.*

For every n > 0 and m > 0, the displayed equation is the multiplied-out form of Yanev's conjecture in A023887, using the frozen primeRadical of D5/S1/Deficit/AlmostAdditivity (A007947), rendered as the named operator primeRadical. Both sides are positive: the radical is positive and each divisor sum includes the divisor one. In particular sigma(1,primeRadical(n)^(m-1)) is positive, so division recovers the stated quotient, with exact natural-number division as well. Sela Fried (2025, Theorem 3) proved the m = 2 case on A001157; the general-m statement is the claim settled here. For prime powers, the equation follows from geometric-sum multiplication identities. Coprime multiplicativity of the radical and divisor sums then extends it to every positive natural number.

## References

- Truth anchor: `D5/S3/Arith/YanevSigmaRadicalIdentity.result`
- Dependency: [D5/S1/Deficit/AlmostAdditivity](../../S1/Deficit/AlmostAdditivity.md)
