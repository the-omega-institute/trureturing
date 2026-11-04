# Trinomial perfect powers over GF(2)

## Abstract

Exact GF(2) trinomial perfect-power counts.

**Definition 1.1 (Kagey's trinomial conjecture).**

$$claim = (\forall (n: Nat), (1 \le n) \Rightarrow (\operatorname{KageyA350532Binomials}.\operatorname{T}\left(2 \cdot n, 3\right) = \operatorname{Nat}.\operatorname{div}\left((n^{2} - n), 2\right)))$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.claim` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2022). *OEIS A350532, sparse perfect powers over Z/2Z*. URL: <https://oeis.org/A350532>.

*Commentary.*

OEIS A350532, unpaginated COMMENT: "Conjecture: T(2*n,3) = (n^2 - n)/2 for n >= 1." The variable n is a natural number. Both subtraction and Nat.div are natural-number operations, with Nat.div denoting integer division. KageyA350532Binomials.T counts distinct nonzero polynomials over ZMod 2.

**Theorem 1.2 (The trinomial count).**

$$\forall (n: Nat), (1 \le n) \Rightarrow (\operatorname{KageyA350532Binomials}.\operatorname{T}\left(2 \cdot n, 3\right) = \operatorname{Nat}.\operatorname{div}\left((n^{2} - n), 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.result` (`✓ std3`). ∎

*Resolves.* `Problems/kagey350532-trinomials` (proved) by `D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kagey350532-trinomials","declaration_gid":"D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Kagey; OEIS Foundation Inc. (2022). *OEIS A350532, sparse perfect powers over Z/2Z*. URL: <https://oeis.org/A350532>.

*Commentary.*

Squaring gives a bijection with degree-n trinomials. Their two lower exponents form a two-element subset of Finset.range n, giving Nat.choose n 2. The binomial-coefficient identity gives the stated natural-number quotient.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.claim`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.result`
- Dependency: [D5/S3/Factorization/Combinatorics/KageyA350532Binomials](KageyA350532Binomials.md)
