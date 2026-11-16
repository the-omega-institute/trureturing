# Column reading preserves every original bond

## Abstract

Actual column decompositions for two-row and three-row diagonal strips.

**Definition 1.1 (Actual three-label columns).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.Column`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.Column` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Column h is Fin(h+1) to Fin 3, without an internal vertical restriction.

**Definition 1.2 (All bonds between consecutive columns).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.cross`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.cross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For each row the two horizontal labels differ. For each pair of adjacent rows the two diagonal label pairs differ. These are exactly the original horizontal and both diagonal edges, with no vertical or wraparound edge.

**Definition 1.3 (Decision for all column cross-bonds).**

$$\forall h: \operatorname{Nat}, (\forall p: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(h\right), (\forall q: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(h\right), ((\operatorname{HardinColumnContinuations}.\operatorname{instDecidableCross}\left(h, p, q\right): \operatorname{Decidable}\left(\operatorname{HardinColumnContinuations}.\operatorname{cross}\left(p, q\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.instDecidableCross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For h : Nat and actual columns p,q : Fin (h+1) to Fin 3, inferInstanceAs decides the conjunction of all horizontal inequalities and both diagonal inequalities at every adjacent row.

**Definition 1.4 (Complete column continuations).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.columnV`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.columnV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The zero-column tail has one filling. At each successor length, sum over all actual next columns satisfying cross. There is no restriction to a representative subset of the graph domain.

**Definition 1.5 (Reversible reading and reconstruction).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.coloringEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.coloringEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Read an actual graph colouring by columns. Conversely place every supplied column entry back at its original cell. The adjacent-column cross conditions supply every graph bond, and both maps are inverse at every positive width and height.

**Definition 1.6 (The two column classes).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.classB`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.classB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Class zero has equal labels and class one has distinct labels. Their actual initial cardinalities are 3 and 6.

**Definition 1.7 (The source B matrix).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.B`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

B=((2,2),(1,0)). All four cross-bonds occur between two-row columns, so the consecutive label supports are disjoint. Each entry is checked for every actual incoming column.

**Definition 1.8 (B continuations).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.vB`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.vB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

vB(0,i)=1 and vB(k+1,i)=sum over j of B(i,j)vB(k,j).

**Definition 1.9 (Every three-row column class).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.classH`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.classH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The four classes are 000; 001 or 011; 010; and 012, up to label permutation. Their exact initial counts are 3,12,6,6. The two equal-adjacent shapes share a class because their continuation counts agree.

**Definition 1.10 (The source H matrix).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.H`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

H=((2,4,2),(1,1,0),(1,0,0)) on the first three classes.

**Definition 1.11 (The isolated class is retained).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.Hfull`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.Hfull` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Hfull has H in its upper-left corner and a zero fourth row and fourth column. An all-distinct column has no successor because the next middle label would have to avoid all three colours. No column can precede it, either. These statements concern actual cross-bonds.

**Definition 1.12 (The three-class source recurrence).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.hV`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.hV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

hV(0,i)=1 and hV(k+1,i)=sum over the three source classes of H(i,j)hV(k,j).

**Definition 1.13 (The complete four-class recurrence).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.vH`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.vH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

vH uses Hfull and has initial value one in every class. Its first three entries equal hV at every length. Its fourth entry is one at length zero and zero at every positive length.

**Theorem 1.14 (Exact column transitions and class sizes).**

$$(\forall p: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(1\right), (\forall j: \operatorname{Fin}\left(2\right), (\sum_{q: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(1\right)} ((\operatorname{if} ((\operatorname{HardinColumnContinuations}.\operatorname{cross}\left(p, q\right)) \land (\operatorname{HardinColumnContinuations}.\operatorname{classB}\left(q\right) = j)) \operatorname{then} (1) \operatorname{else} (0))) = \operatorname{HardinColumnContinuations}.\operatorname{B}\left(\operatorname{HardinColumnContinuations}.\operatorname{classB}\left(p\right), j\right)))) \land ((\forall p: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(2\right), (\forall j: \operatorname{Fin}\left(4\right), (\sum_{q: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(2\right)} ((\operatorname{if} ((\operatorname{HardinColumnContinuations}.\operatorname{cross}\left(p, q\right)) \land (\operatorname{HardinColumnContinuations}.\operatorname{classH}\left(q\right) = j)) \operatorname{then} (1) \operatorname{else} (0))) = \operatorname{HardinColumnContinuations}.\operatorname{Hfull}\left(\operatorname{HardinColumnContinuations}.\operatorname{classH}\left(p\right), j\right)))) \land ((\forall j: \operatorname{Fin}\left(2\right), (\sum_{p: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(1\right)} ((\operatorname{if} (\operatorname{HardinColumnContinuations}.\operatorname{classB}\left(p\right) = j) \operatorname{then} (1) \operatorname{else} (0))) = (![3, 6]: \operatorname{Fin}\left(2\right) \to \operatorname{Nat})\left(j\right))) \land (\forall j: \operatorname{Fin}\left(4\right), (\sum_{p: \operatorname{HardinColumnContinuations}.\operatorname{Column}\left(2\right)} ((\operatorname{if} (\operatorname{HardinColumnContinuations}.\operatorname{classH}\left(p\right) = j) \operatorname{then} (1) \operatorname{else} (0))) = (![3, 12, 6, 6]: \operatorname{Fin}\left(4\right) \to \operatorname{Nat})\left(j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.column_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every actual column, the successor counts equal B or Hfull at its class. The two-row class sizes are 3 and 6; the three-row class sizes are 3, 12, 6 and 6. The Hfull transition and size projections supply the zero-defect sectors of HardinA229536Strip after its exact budget and class cut and the natural-to-integer cast.

**Theorem 1.15 (Exact universal B and H interpretations).**

$$\forall k: \operatorname{Nat}, \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{true}, 1, k\right), \operatorname{Fin}\left(3\right)\right)\right) = 3 \cdot \operatorname{vB}\left(k, 0\right) + 6 \cdot \operatorname{vB}\left(k, 1\right) \land \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{true}, 2, k\right), \operatorname{Fin}\left(3\right)\right)\right) = 3 \cdot \operatorname{hV}\left(k, 0\right) + 12 \cdot \operatorname{hV}\left(k, 1\right) + 6 \cdot \operatorname{hV}\left(k, 2\right) + \operatorname{ite}\left(k = 0, 6, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.column_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The variable k is the number of appended columns, so the actual width is k+1. The equations hold for every k≥0 on the original two-row and three-row strip graphs. Reading columns and splitting off the first one gives the exact graph count. The finite class certificates then feed induction on every continuation length. Consequently B and H have the displayed source interpretations, independently of terminal generating-series equality. At k=0 the three-row count is 3+12+6+6=27, and the literal normalized count is 11. For positive k the isolated contribution vanishes, giving precisely the source H expression for widths at least two. The width-one correction is part of the formula.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.B`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.Column`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.H`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.Hfull`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.classB`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.classH`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.coloringEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.columnV`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.column_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.column_result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.cross`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.hV`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.instDecidableCross`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.vB`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.vH`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](HardinThinGraphTransport.md)
