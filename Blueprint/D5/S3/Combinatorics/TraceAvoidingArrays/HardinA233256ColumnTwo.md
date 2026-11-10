# A233256 ColumnTwo

## Abstract

Hardin's ColumnTwo recurrence for literal normalized six-colour arrays.

For each row, the horizontal bond joins its two cells. The antidiagonal bond joins the right cell to the left cell of the next row. These are all the bonds. Row-major normalization uses the shared scanner. The boundary records the right-cell pair label and the seen-colour flags. Reachable continuations satisfy a quadratic identity with coefficients 20 and minus 64. Fin.val denotes the natural value of a finite index or colour. Exact initial counts give the recurrence at its first admissible index; the transfer identity gives every later case.

**Definition 1.1 (The literal filtered array count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnTwo}.\operatorname{a}\left(n\right) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233123SquareStrip}.\operatorname{rowLegal}, (\lambda (c: \operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(6\right)) \mapsto (\lambda (d: \operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(6\right)) \mapsto (c\left((1: \operatorname{Fin}\left(2\right))\right) \ne d\left((0: \operatorname{Fin}\left(2\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left((0: \operatorname{Fin}\left(2\right))\right)\right)) \ne 5))), A\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233256: horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233256>.

*Commentary.*

The literal filtered array count.

**Theorem 1.2 (Exact initial counts).**

$$((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnTwo}.\operatorname{a}\left(1\right): \operatorname{Int}) = 1) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnTwo}.\operatorname{a}\left(2\right): \operatorname{Int}) = 10) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnTwo}.\operatorname{a}\left(3\right): \operatorname{Int}) = 136))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233256: horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233256>.

*Commentary.*

Exact initial counts.

**Theorem 1.3 (The integer recurrence).**

$$\forall (n: \operatorname{Nat}), ((3 \le n) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnTwo}.\operatorname{a}\left(n\right): \operatorname{Int}) = ((20) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnTwo}.\operatorname{a}\left((n) - (1)\right): \operatorname{Int}))) - ((64) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnTwo}.\operatorname{a}\left((n) - (2)\right): \operatorname{Int})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233256: horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233256>.

*Commentary.*

The integer recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip](HardinA233123SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
