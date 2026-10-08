# Maximum Length of a Two-Dense Divisor Block

## Abstract

The largest two-dense divisor block has ruler-scaled maximum odd count.

Both statistics use the complete increasing list of positive divisors and its actual maximal splitBy blocks. An adjacent pair a,b stays joined exactly when b is at most twice a. Equality and singleton blocks are retained. The theorem includes every positive natural n.

**Definition 1.1 (Odd counts in the actual blocks).**

$$\forall n: \mathbb{N}, \operatorname{oddBlockCounts}(n) = \operatorname{map}((B \mapsto \operatorname{length}(\operatorname{filter}((d \mapsto \operatorname{decide}(\operatorname{Odd}(d))), B))), \operatorname{splitBy}((a b \mapsto \operatorname{decide}(b \le 2\cdot a)), \operatorname{map}(\operatorname{fst}, \operatorname{divisorsAntidiagonalList}(n))))$$

*Formalization.* `D5/S3/Factorization/TwoDenseDivisorBlockMaximum.oddBlockCounts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count odd entries in each block of the same partition used by the existing row function. At n=0 Mathlib's divisor list is empty.

**Theorem 1.2 (The maximum identity).**

$$\forall n: \mathbb{N}, 0 < n \implies \operatorname{sup}(\operatorname{toFinset}(\operatorname{row}(n)), \operatorname{id}) = (\operatorname{factorization}(n, 2) + 1) \cdot \operatorname{sup}(\operatorname{toFinset}(\operatorname{oddBlockCounts}(n)), \operatorname{id})$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TwoDenseDivisorBlockMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a400194-two-dense-divisor-block-maximum` (proved) by `D5/S3/Factorization/TwoDenseDivisorBlockMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a400194-two-dense-divisor-block-maximum","declaration_gid":"D5/S3/Factorization/TwoDenseDivisorBlockMaximum.result","resolution_kind":"proved"} -->

*Citation.* Omar E. Pol (2026). *OEIS A400194, maximum length of a two-dense divisor block*. URL: <https://oeis.org/A400194>.

*Commentary.*

Sortedness and the strict separating boundaries show that divisor-list endpoints whose ratio is at most two have the same block membership. Every complete dyadic chain of an odd divisor therefore remains inside one actual block. The map from an odd member and an exponent between zero and factorization(n,2) to their dyadic product bijects onto that block. Odd-component recovery, cancellation and injectivity of powers of two prove injectivity. Distinct divisor entries turn the bijection into the local block-length identity. Taking suprema over the same block family gives the conjectured maximum formula. The zero default of the natural supremum is harmless; every positive n has divisor one.

## References

- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlockMaximum.oddBlockCounts`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlockMaximum.result`
- Dependency: [D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome](TwoDenseDivisorBlocksPalindrome.md)
