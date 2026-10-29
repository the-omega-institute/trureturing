# BalaA363411TypeOne

## Abstract

Integer quadratic products and Bala's valuation conjectures.

**Definition 1.1 (The type-one primes through 101).**

$$\operatorname{claim} = \left(\forall p \in \mathbb{N},\; (p \le 101) \Rightarrow (((\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \land (\forall n \in \mathbb{N},\; \neg ((p : \mathbb{Z}) \mid \operatorname{BalaA363411}.\operatorname{a}\left(n\right)))) \Leftrightarrow p \in (\{3, 11, 17, 23, 29, 41, 47, 53, 59, 83, 89, 101\} : \operatorname{Finset}\left(\mathbb{N}\right)))\right)$$

*Formalization.* `D5/S3/Arith/Congruence/BalaA363411TypeOne.claim` (`✓ std3`).

*Citation.* P. Bala (2023). *OEIS A363411 and A363412 — quadratic integer product coordinates*. URL: <https://oeis.org/A363411>.

*Commentary.*

OEIS A363411, COMMENTS (revision 18, no page): "Type 1: primes that do not divide any element of the sequence {a(n)}." "We conjecture that the set of type 1 primes begins {3, 11, 17, 23, 29, 41, 47, 53, 59, 83, 89, 101, ...}." Here the initial list means exactly these primes through 101; the term index is unbounded.

**Theorem 1.2 (The complete initial type-one list).**

$$\forall p \in \mathbb{N},\; (p \le 101) \Rightarrow (((\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \land (\forall n \in \mathbb{N},\; \neg ((p : \mathbb{Z}) \mid \operatorname{BalaA363411}.\operatorname{a}\left(n\right)))) \Leftrightarrow p \in (\{3, 11, 17, 23, 29, 41, 47, 53, 59, 83, 89, 101\} : \operatorname{Finset}\left(\mathbb{N}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BalaA363411TypeOne.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala3634-type-one` (proved) by `D5/S3/Arith/Congruence/BalaA363411TypeOne.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala3634-type-one","declaration_gid":"D5/S3/Arith/Congruence/BalaA363411TypeOne.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Bala (2023). *OEIS A363411 and A363412 — quadratic integer product coordinates*. URL: <https://oeis.org/A363411>.

*Commentary.*

For each listed prime other than 3, the full coefficient block is (2,0) and its real coordinates below the prime are nonzero. Strong induction extends nonvanishing to every index. The real coordinate modulo 3 is always one. Each other prime at most 101 has a finite zero-coordinate certificate, including the prime 2.

## References

- Truth anchor: `D5/S3/Arith/Congruence/BalaA363411TypeOne.claim`
- Truth anchor: `D5/S3/Arith/Congruence/BalaA363411TypeOne.result`
- Dependency: [D5/S3/Arith/Congruence/BalaA363411](BalaA363411.md)
