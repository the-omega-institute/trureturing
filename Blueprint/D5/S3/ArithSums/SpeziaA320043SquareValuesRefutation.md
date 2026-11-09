# Spezia's A320043 square-value conjecture is false

## Abstract

A prime row and the Pell equation give an additional square value of OEIS A320043.

**Definition 1.1 (The gcd-weighted row sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, n\right)} \operatorname{Nat}.\operatorname{div}\left((n + 1 - k)^{2} \cdot k, \operatorname{Nat}.\operatorname{gcd}\left(n + 1 - k, k\right)^{3}\right)$$

*Formalization.* `D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.a` (`✓ std3`).

*Citation.* Stefano Spezia; OEIS Foundation Inc. (2018). *OEIS A320043: Row sums of the triangle A322550*. URL: <https://oeis.org/A320043/internal>.

*Commentary.*

OEIS A320043, revision 43, first FORMULA (unpaginated): "a(n) = Sum_{k=1..n} (n + 1 - k)^2*k/gcd(n + 1 - k, k)^3." Here n and k are natural numbers. Nat.div is natural-number division, and subtraction is natural subtraction. For 1 <= k <= n, both gcd arguments are positive and the denominator divides the numerator exactly. The value at n = 0 is the empty sum; the source starts at n = 1.

**Definition 1.2 (The source conjecture).**

$$claim = \left(\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall m \in \mathbb{N},\; (\operatorname{a}\left(n\right) = m^{2}) \Rightarrow ((n = 1) \lor ((n = 6) \lor (n = 96))))\right)$$

*Formalization.* `D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.claim` (`✓ std3`).

*Citation.* Stefano Spezia; OEIS Foundation Inc. (2018). *OEIS A320043: Row sums of the triangle A322550*. URL: <https://oeis.org/A320043/internal>.

*Commentary.*

OEIS A320043, revision 43, sole COMMENTS conjecture (unpaginated): "Conjecture: a(n) is not a perfect square except for n = 1, 6 and 96." The positive index n and the square root m range over natural numbers. The OFFSET field is 1,2; its first entry supplies the positive-index domain.

**Theorem 1.3 (An additional square refutes the conjecture).**

$$\neg (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall m \in \mathbb{N},\; (\operatorname{a}\left(n\right) = m^{2}) \Rightarrow ((n = 1) \lor ((n = 6) \lor (n = 96)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/a320043-square-values-refutation` (refuted) by `D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"a320043-square-values-refutation","declaration_gid":"D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stefano Spezia; OEIS Foundation Inc. (2018). *OEIS A320043: Row sums of the triangle A322550*. URL: <https://oeis.org/A320043/internal>.

*Commentary.*

Take p = 708158977 and y = 204427888. Lucas's criterion proves p prime, and p squared minus 12 times y squared equals 1. For prime p, gcd(p-k,k) equals 1 on 1 <= k < p. A polynomial telescope gives 12*a(p-1) = p squared times (p squared minus 1), so the Pell equation gives a(p-1) = (p*y) squared. Thus a(708158976) equals 144767444036350576 squared. This positive index differs from 1, 6 and 96. Minimality, infinitely many prime Pell inputs, and classification of other square values remain open.

## References

- Truth anchor: `D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.a`
- Truth anchor: `D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.claim`
- Truth anchor: `D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.result`
