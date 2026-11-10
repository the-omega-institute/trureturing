# A233256 ColumnOne

## Abstract

Hardin's ColumnOne recurrence for literal normalized six-colour arrays.

One column has no horizontal or antidiagonal bonds. The first cell is zero. Each 2, 3 or 4 has a strictly earlier 1, and each 3 a strictly earlier 2. The public row transfer at width one counts these words. The continuation vectors satisfy a cubic identity with coefficients 12, minus 44 and 48; linearity propagates the finite state identity to all lengths. Fin.val denotes the natural value of a finite index or colour. Exact initial counts give the recurrence at its first admissible index; the transfer identity gives every later case.

**Definition 1.1 (The literal filtered array count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left(n\right) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(1\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(1\right) \to \operatorname{Fin}\left(6\right), \operatorname{True}\right), \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(1\right) \to \operatorname{Fin}\left(6\right), \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(1\right) \to \operatorname{Fin}\left(6\right), \operatorname{True}\right)\right), A\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(1\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233256: horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233256>.

*Commentary.*

The literal filtered array count.

**Theorem 1.2 (Exact initial counts).**

$$((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left(1\right): \operatorname{Int}) = 1) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left(2\right): \operatorname{Int}) = 3) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left(3\right): \operatorname{Int}) = 11) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left(4\right): \operatorname{Int}) = 48)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233256: horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233256>.

*Commentary.*

Exact initial counts.

**Theorem 1.3 (The integer recurrence).**

$$\forall (n: \operatorname{Nat}), ((4 \le n) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left(n\right): \operatorname{Int}) = (((12) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left((n) - (1)\right): \operatorname{Int}))) - ((44) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left((n) - (2)\right): \operatorname{Int})))) + ((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233256ColumnOne}.\operatorname{a}\left((n) - (3)\right): \operatorname{Int})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233256-columnone` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233256-columnone","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233256: horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233256>.

*Commentary.*

The integer recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
