# Five-row HDA transfers with one residual defect

## Abstract

Five-row HDA transfers with one residual defect

A boundary stores the five entries in one column. Every bond crosses to the next column at the same row or an adjacent row.

**Definition 1.1 (edges).**

$$(\operatorname{HardinA229538StripData}.\operatorname{edges}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)) = \operatorname{Finset}.\operatorname{filter}\left((\lambda ((r, s): (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right)))\mapsto (\operatorname{Fin}.\operatorname{val}\left(s\right) = \operatorname{Fin}.\operatorname{val}\left(r\right) \lor \left(\operatorname{Fin}.\operatorname{val}\left(s\right) = \operatorname{Fin}.\operatorname{val}\left(r\right) + 1 \lor \operatorname{Fin}.\operatorname{val}\left(r\right) = \operatorname{Fin}.\operatorname{val}\left(s\right) + 1\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.edges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The oriented cut is the set of pairs of row indices that form a bond between columns zero and one.

**Definition 1.2 (cost).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right): \operatorname{Nat}) = \operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229538StripData}.\operatorname{edges}, \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(q\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.cost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The cost is the number of monochromatic bonds on the cut between two decoded columns.

**Theorem 1.3 (bondDefects_empty).**

$$\forall (r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)), r, r\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.bondDefects_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The number of monochromatic bonds of a row against itself over the empty edge set is zero.

**Theorem 1.4 (cost_zero).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right) = 0) \Leftrightarrow (\operatorname{HardinA233178Chromatic}.\operatorname{Bond}\left(p, q\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.cost_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

A cut has cost zero exactly when every bond has different colours at its endpoints.

**Theorem 1.5 (zero_cost_entry).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{if} (\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right) = 0) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0) = \operatorname{HardinA233178Chromatic}.\operatorname{T}\left(p, q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.zero_cost_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The proper-colouring transfer entry is the indicator of a cut without monochromatic bonds.

**Definition 1.6 (oneDefect).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538StripData}.\operatorname{oneDefect}\left(p, q\right): \operatorname{Int}) = (\operatorname{if} (\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right) = 1) \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.oneDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

Each entry is the indicator of a cut with exactly one monochromatic bond.

**Definition 1.7 (transfer).**

$$(\operatorname{HardinA229538StripData}.\operatorname{transfer}: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{Int}\right)) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233178Chromatic}.\operatorname{T}, \operatorname{HardinA229538StripData}.\operatorname{oneDefect}, (0: \operatorname{Matrix}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Int}\right)), \operatorname{HardinA233178Chromatic}.\operatorname{T}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The two summands represent one and zero residual defects. A legal cut preserves the budget and a cut of cost one moves from the first summand to the second.

**Definition 1.8 (terminal).**

$$(\operatorname{HardinA229538StripData}.\operatorname{terminal}: \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right) \to \operatorname{Int}) = \operatorname{Sum}.\operatorname{elim}\left((0: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The empty continuation completes an array exactly when its remaining budget is zero.

**Theorem 1.9 (transfer_readout).**

$$\forall (S: \operatorname{Type}*), ([\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] \forall (M: \operatorname{Matrix}\left(S, S, \operatorname{Int}\right)), (\forall (u: S \to \operatorname{Int}), (\forall (v: S \to \operatorname{Int}), (\forall (d: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Fin}\left(d\right) \to \operatorname{Int}), ((\operatorname{Matrix}.\operatorname{mulVec}\left(M^{b + d}, u\right) = \sum_{(j: \operatorname{Fin}\left(d\right))} (\operatorname{SMul}.\operatorname{smul}\left(c\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left(M^{b + \operatorname{Fin}.\operatorname{val}\left(j\right)}, u\right)\right))) \Rightarrow (\forall (n: \operatorname{Nat}), (\operatorname{dotProduct}\left(v, \operatorname{Matrix}.\operatorname{mulVec}\left(M^{n + b + d}, u\right)\right) = \sum_{(j: \operatorname{Fin}\left(d\right))} (c\left(j\right) \cdot \operatorname{dotProduct}\left(v, \operatorname{Matrix}.\operatorname{mulVec}\left(M^{n + b + \operatorname{Fin}.\operatorname{val}\left(j\right)}, u\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.transfer_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The state type belongs to an arbitrary universe. A vector recurrence for a matrix and terminal vector gives a shifted scalar recurrence for every readout vector.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.bondDefects_empty`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.cost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.cost_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.edges`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.oneDefect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.transfer_readout`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.zero_cost_entry`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
