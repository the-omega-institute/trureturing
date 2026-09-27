# The Stechkin Function Divisor-Count Formula

## Abstract

The Stechkin function counts a divisibility condition that splits into divisors of two adjacent integers.

All variables take values in the natural numbers N. The operator NatDiv is Euclidean natural-number division, so it is the floor of the corresponding nonnegative rational quotient. The operator Icc gives a closed finite interval, filter retains the elements satisfying its predicate, and card denotes finite-set cardinality.

**Definition 1.1 (The Stechkin counting function).**

$$\forall n \in \mathbb{N},\; \operatorname{stechkinFunction}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{Icc}\left(2, n\right), m \mapsto m - 1 \mid \operatorname{NatDiv}\left(n \cdot \left(m - 1\right), m\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/StechkinFunctionDivisorCount.stechkinFunction` (`✓ std3`).

*Citation.* Robert Israel; Ridouane Oudra (2020). *OEIS A274010: the Boris Stechkin function and an adjacent divisor-count formula*. URL: <https://oeis.org/A274010>.

*Commentary.*

For each n, the function counts exactly the integers m from two through n for which m-1 divides the Euclidean quotient of n(m-1) by m.

**Theorem 1.2 (The adjacent divisor-count identity).**

$$\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \operatorname{stechkinFunction}\left(n\right) + 2 = \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right) + \operatorname{card}\left(\operatorname{divisors}\left(n - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/StechkinFunctionDivisorCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a274010-stechkin-divisor-count` (proved) by `D5/S3/Arith/StechkinFunctionDivisorCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a274010-stechkin-divisor-count","declaration_gid":"D5/S3/Arith/StechkinFunctionDivisorCount.result","resolution_kind":"proved"} -->

*Citation.* Robert Israel; Ridouane Oudra (2020). *OEIS A274010: the Boris Stechkin function and an adjacent divisor-count formula*. URL: <https://oeis.org/A274010>.

*Commentary.*

For n at least two, reindexing by k=m-1 turns the filtered predicate into the disjoint union of the nontrivial divisors of n and n-1. Each full divisor set also contains one, so restoring those two omitted elements gives the displayed equality.

## References

- Truth anchor: `D5/S3/Arith/StechkinFunctionDivisorCount.result`
- Truth anchor: `D5/S3/Arith/StechkinFunctionDivisorCount.stechkinFunction`
