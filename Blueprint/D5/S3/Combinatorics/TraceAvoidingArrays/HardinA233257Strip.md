# The normalized two-row antidiagonal strip

## Abstract

Closed form and generating function for the two-row antidiagonal strip.

The strip has horizontal bonds in both rows and a bond from the lower cell of a column to the upper cell of the next column. Bonded colours differ and do not sum to five. The first cell is zero. Row-major order puts the whole upper row before the lower row. Normalization is the predicate D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.normal. The empty coefficient is zero. All formula names are full Lean names; Fin.val and Int.ofNat display the relevant coercions.

**Definition 1.1 (Literal bond and normalization predicate).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{Legal}\left(A\right) = ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(2\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), ((\forall (r: \operatorname{Fin}\left(2\right)), ((A\left((r, j)\right) \ne A\left((r, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((r, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right)\right)) \ne 5))) \land ((A\left(((1: \operatorname{Fin}\left(2\right)), j)\right) \ne A\left(((0: \operatorname{Fin}\left(2\right)), \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left(((1: \operatorname{Fin}\left(2\right)), j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left(((0: \operatorname{Fin}\left(2\right)), \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right))\right)\right)) \ne 5))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.Legal` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233257: two-row horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233257>.

*Commentary.*

Literal bond and normalization predicate.

**Definition 1.2 (Literal filtered count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{Legal}\left(A\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233257: two-row horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233257>.

*Commentary.*

Literal filtered count.

**Theorem 1.3 (The empty and one-column coefficients).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left(0\right) = 0) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left(1\right) = 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233257: two-row horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233257>.

*Commentary.*

The empty and one-column coefficients.

**Theorem 1.4 (Barker's closed form).**

$$\forall (n: \operatorname{Nat}), ((9) \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (2)\right)) = (2^{((2) \cdot (n)) + (1)}) \cdot (((4) \cdot (3^{(n) + (2)})) + (9)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233257: two-row horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233257>.

*Commentary.*

Barker's closed form.

**Theorem 1.5 (Hardin's integer recurrence).**

$$\forall (n: \operatorname{Nat}), (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (4)\right)\right) = (((16: \operatorname{Int})) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (3)\right)\right))) - (((48: \operatorname{Int})) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (2)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233257: two-row horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233257>.

*Commentary.*

Hardin's integer recurrence.

**Theorem 1.6 (Barker's generating function with the closed form and recurrence).**

$$(((((1: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) - (((4: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) \cdot (((1: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) - (((12: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))))) \cdot ((\operatorname{PowerSeries}.\operatorname{mk}\left((\lambda (n: \operatorname{Nat}) \mapsto \operatorname{Int}.\operatorname{ofNat}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left(n\right)\right))\right): \operatorname{PowerSeries}\left(\operatorname{Int}\right))) = ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((((3: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) - (((38: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + (((88: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))^{2})))) \land ((\forall (n: \operatorname{Nat}), ((9) \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (2)\right)) = (2^{((2) \cdot (n)) + (1)}) \cdot (((4) \cdot (3^{(n) + (2)})) + (9)))) \land (\forall (n: \operatorname{Nat}), (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (4)\right)\right) = (((16: \operatorname{Int})) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (3)\right)\right))) - (((48: \operatorname{Int})) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233257Strip}.\operatorname{a}\left((n) + (2)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233257` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233257","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233257: two-row horizontal and antidiagonal complementary-pair exclusion*. URL: <https://oeis.org/A233257>.

*Commentary.*

Barker's generating function with the closed form and recurrence.

The pair-label map D5.S3.Observer.Separation.BooleanRankThreeK4.beta turns every bond into label inequality. For width n+2, the last-column transfer distinguishes equal and unequal labels within a column. Its matrix has rows (2,2) and (1,1), and its initial weights are (12,12). These weights form a left eigenvector with eigenvalue three. Mathlib's eigenvector power theorem gives 24 times 3 to the power n proper three-label patterns. If a label is omitted, the three-label bond constraints force every column to be constant. Replicating the upper row four times gives an array to which D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.two_label_classification applies. Restricting its alternating pattern and identifying the lower row gives exactly six two-label patterns. The frozen canonical_pattern_card and normalized_card theorems of D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical give four times 3 to the power n canonical patterns, one of them with two labels. Their lift weights give the closed form. Expanding the two geometric factors gives the integer recurrence and the coefficient identity. Hardin authored the sequence and empirical recurrence; Barker stated the closed form and generating function.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.closed_form`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.recurrence`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder](HardinA233177Ladder.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
