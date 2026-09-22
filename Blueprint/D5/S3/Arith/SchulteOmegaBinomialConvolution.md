# Schulte's Omega Binomial Convolution

## Abstract

Schulte's binomial convolution relates the total and distinct prime-factor counts.

C denotes the complex numbers and N the natural numbers including zero. Omega, written Ω, is A001222, the number of prime factors counted with multiplicity; omega, written ω, is A001221, the number of distinct prime factors. Their difference is A046660. Subtraction in the exponent is natural-number subtraction; omega(n) is at most Omega(n), so no truncation changes this difference. The sum ranges over all positive divisors d of n, including one and n. The slash n/d denotes natural-number division, which is exact on this divisor set. Powers have natural exponents, including the convention 0^0 = 1. Only Schulte's general x, y conjecture for positive n is asserted here. The case x = 1 - y is the Dressler-van de Lune 1973 result; other OEIS assertions are outside the claim.

**Theorem 1.1 (The binomial divisor convolution).**

$$\forall x \in \mathbb{C}, \forall y \in \mathbb{C}, \forall n \in \mathbb{N}, (0 < n) \implies ((x + y)^{\operatorname{Omega}\left(n\right)} = \sum_{d \mid n} x^{\operatorname{Omega}\left(d\right)} \cdot ((x + y)^{\operatorname{Omega}\left(n / d\right) - \operatorname{omega}\left(n / d\right)} \cdot y^{\operatorname{omega}\left(n / d\right)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteOmegaBinomialConvolution.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a001222-schulte-omega-binomial-convolution` (proved) by `D5/S3/Arith/SchulteOmegaBinomialConvolution.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a001222-schulte-omega-binomial-convolution","declaration_gid":"D5/S3/Arith/SchulteOmegaBinomialConvolution.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2018). *OEIS A001222, the Ω/ω binomial convolution conjecture (x+y)^Ω(n) = Σ_{d|n} x^Ω(d) (x+y)^{Ω(n/d)−ω(n/d)} y^{ω(n/d)}*. URL: <https://oeis.org/A001222>.

*Commentary.*

Both sides define multiplicative arithmetic functions after setting their values at zero to zero. On each prime power the convolution becomes a finite geometric sum. Its polynomial identity holds even when y or x+y is zero. Equality on prime powers then gives the identity at every positive natural index.

## References

- Truth anchor: `D5/S3/Arith/SchulteOmegaBinomialConvolution.result`
