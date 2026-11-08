# Binomial perfect powers over GF(2)

## Abstract

Exact GF(2) sparse perfect-power counts.

**Definition 1.1 (The sparse proper-power count).**

$$\forall (n: Nat), \forall (k: Nat), \operatorname{T}\left(n, k\right) = \operatorname{Nat}.\operatorname{card}\left(\{p: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right) // (p \ne 0) \land ((\operatorname{Polynomial}.\operatorname{natDegree}\left(p\right) = n) \land ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Polynomial}.\operatorname{support}\left(p\right)\right) = k) \land (\exists (f: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), \exists (m: Nat), (1 < m) \land (p = f^{m}))))\}\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.T` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2022). *OEIS A350532, sparse perfect powers over Z/2Z*. URL: <https://oeis.org/A350532>.

*Commentary.*

OEIS A350532, unpaginated NAME: "Triangle read by rows: T(n,k) is the number of degree-n polynomials over Z/2Z of the form f(x)^m for some m > 1 with exactly k nonzero terms; 1 <= k <= n + 1." Here n and k are natural numbers, Polynomial (ZMod 2) is the polynomial ring, and Nat.card counts distinct nonzero polynomials rather than representations as powers. The displayed expression also defines T outside the triangular range.

**Definition 1.2 (Kagey's binomial conjecture).**

$$claim = (\forall (n: Nat), \operatorname{T}\left(2 \cdot n, 2\right) = n)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.claim` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2022). *OEIS A350532, sparse perfect powers over Z/2Z*. URL: <https://oeis.org/A350532>.

*Commentary.*

OEIS A350532, unpaginated COMMENT: "Conjecture: T(2*n,2) = n." The variable n ranges over all natural numbers, including zero.

**Theorem 1.3 (Two- and three-term counts).**

$$\forall (n: Nat), \forall (k: Nat), (1 \le k) \Rightarrow ((k \le 2) \Rightarrow (\operatorname{T}\left(2 \cdot n, k + 1\right) = \operatorname{Nat}.\operatorname{choose}\left(n, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.card_sparse_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Kagey; OEIS Foundation Inc. (2022). *OEIS A350532, sparse perfect powers over Z/2Z*. URL: <https://oeis.org/A350532>.

*Commentary.*

A proper power with two or three nonzero terms has an even exponent. After removing the maximal power of X, the derivative and descent under exponent contraction rule out odd proper powers. Squaring doubles every exponent and preserves support size, so contraction identifies the counted polynomials with degree-n polynomials having k+1 terms. Erasing the leading exponent identifies their supports with k-element subsets of Finset.range n. This count also holds when n is zero.

**Theorem 1.4 (The binomial count).**

$$\forall (n: Nat), \operatorname{T}\left(2 \cdot n, 2\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.result` (`✓ std3`). ∎

*Resolves.* `Problems/kagey350532-perfectpowers` (proved) by `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kagey350532-perfectpowers","declaration_gid":"D5/S3/Factorization/Combinatorics/KageyA350532Binomials.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Kagey; OEIS Foundation Inc. (2022). *OEIS A350532, sparse perfect powers over Z/2Z*. URL: <https://oeis.org/A350532>.

*Commentary.*

The two-term case has exactly n possibilities in degree 2*n. Each is the square of a degree-n polynomial with two terms; the lower exponent can be any natural number strictly below n.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.T`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.card_sparse_powers`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.claim`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KageyA350532Binomials.result`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](../../../S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.md)
