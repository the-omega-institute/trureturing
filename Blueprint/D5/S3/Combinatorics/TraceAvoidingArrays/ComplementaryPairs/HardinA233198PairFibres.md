# Eight colours and four complementary pairs

## Abstract

Ordered complementary-pair fibres for literal width-four eight-colour arrays.

**Definition 1.1 (The full generating-function proposition).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{GeneratingFunction}\left(\right)) \Leftrightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{A}\left(\right) = ((\operatorname{PowerSeries}.\operatorname{X}) \cdot ((((((11) - ((1760) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1}))) + ((99328) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) - ((3080192) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3}))) + ((55050240) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{4}))) - ((369098752) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{5})))) \cdot (\left(((1) - ((16) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1}))) \cdot (((((1) - ((192) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1}))) + ((10240) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) - ((278528) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3}))) + ((4194304) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{4})))\right)^{-1}))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.GeneratingFunction` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Division means formal inversion in rational power series.

A cell is a pair in Fin n times Fin 4, and its row-major rank is four times its first natural label plus its second. Fin.val is the natural label of a finite element. Natural-number sums are used for the exclusion of complementary colours. The three directed edge representatives describe precisely the contained horizontal, vertical and antidiagonal bonds.

**Theorem 1.2 (The two-colour boundary).**

$$\forall (n: \operatorname{Nat}), ((0 < n) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(2, n\right) = \operatorname{ite}\left(n = 1, 2, 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.ordinary_two_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

At height one the graph is a path. Every larger height contains the triangle on cells (0,0), (0,1), (1,0), which excludes two colours.

**Theorem 1.3 (The three-colour classification).**

$$\forall (n: \operatorname{Nat}), ((0 < n) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(3, n\right) = \operatorname{ite}\left(n = 1, 24, 6\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.ordinary_three_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

At height one there are twenty-four proper rows. For a row that has a compatible neighbour, the three distinct colours force the pattern (a,b,c,a); the unique successor is (c,a,b,c). The kernel-checked local compatibility certificate and continuation induction give six colourings at every larger height.

**Theorem 1.4 (The four-colour formal series).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinarySeries}\left(4\right) = (((((108) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1})) - ((528) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) + ((960) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3}))) - ((1200) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{4}))) \cdot (\left(((((1) - ((12) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1}))) + ((40) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) - ((68) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3}))) + ((64) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{4}))\right)^{-1})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.ordinary_series_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Proper rows have the five equality patterns 0101, 0102, 0120, 0121, 0123. Their compatibility test compares equal columns and the old column j+1 with the new column j. The complete finite row table and initial row-pair distribution are checked by kernel reduction. The general continuation transfer is applied after a bijection from the exact graph's proper maps to proper-row words. A kernel-checked fourth-order matrix relation gives the recurrence at every applicable height. Coefficientwise multiplication then proves the formal-series identity; the denominator is a unit because its constant coefficient is one.

**Theorem 1.5 (The literal all-height identity).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{A}\left(\right) = ((\operatorname{PowerSeries}.\operatorname{X}) \cdot ((((((11) - ((1760) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1}))) + ((99328) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) - ((3080192) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3}))) + ((55050240) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{4}))) - ((369098752) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{5})))) \cdot (\left(((1) - ((16) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1}))) \cdot (((((1) - ((192) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{1}))) + ((10240) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) - ((278528) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3}))) + ((4194304) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{4})))\right)^{-1})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.generating_function` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Rescale the ordinary four-colour series by sixteen. The weighted count identifies the coefficients of 384 A minus that rescaled series: zero in degree zero, 2496 in degree one, and 384 times sixteen to the power n minus one in every degree n at least two. Multiplication by one minus sixteen X leaves 2496 X minus 33792 X squared. The rescaled four-colour denominator and numerator then give the entire displayed polynomial identity. Its denominator has constant coefficient one, so formal inversion is valid. The coefficient definition of A retains exactly the literal positive-height arrays, including the height-one boundary and unused colours.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.GeneratingFunction`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.generating_function`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.ordinary_series_four`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.ordinary_three_count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.ordinary_two_count`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel](HardinA233198LiteralModel.md)
