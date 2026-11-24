# Exact two-defect strip transfer

## Abstract

Exact two-defect strip transfer.

**Definition 1.1 (Classes at budget zero).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\operatorname{\mathit{exhaustedClass}}\left(p\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{Valid}}\left(p, 1\right)) \operatorname{\mathit{then}} \operatorname{\mathit{oldZeroImage}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, 0\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(56, \operatorname{\mathit{Fin}}.\operatorname{\mathit{ofNat}}\left(40, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{fresh}}\left(p\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhaustedClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

If Valid(p,1) holds, let i be the value of the A229585 class of p at budget zero. The return value is i minus 16 in Fin 96 when i is at least 16, and zero otherwise. If Valid(p,1) fails, use the A229635 first-occurrence equality-pattern index. Its first 40 entries are the lexicographically ordered canonical six-cell boundaries with exactly two adjacent equalities. Fin.ofNat 40 takes the residue of its natural-valued input modulo 40. Fin.natAdd 56 embeds the residue with offset 56. A pattern absent from the 40 entries in this branch has more than two adjacent equalities. Its equality mask is absent from the 96 A229635 representatives, whose lookup returns 96 before reduction modulo 96. The resulting index is zero, so the exhausted class is 56.

**Definition 1.2 (Class of a boundary and budget).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (d = 0) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, \operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{exhaustedClass}}\left(p\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(96, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A positive budget d uses the A229585 boundary class at budget d minus one.

**Definition 1.3 (Column indices of the exhausted block).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{exitRead}} : (\operatorname{\mathit{Fin}}\left(96\right)) \to (\operatorname{\mathit{Fin}}\left(108\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exitRead` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

For the 56 active sources outside the zeroBudgetClass image and the 40 new exhausted sources, this 96-entry map selects the readout coordinate. Values below 72 index the old leading row for those active sources and the zero prefix for new exhausted sources. Otherwise its value minus 72 is one of 36 radix-16 digit positions in the packed word selected by the source row. The tables store 56 active words and 38 distinct exhausted words. The successor formula pins the entries to their destination classes.

**Definition 1.4 (Transfer matrix).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T} : \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(168\right), \operatorname{\mathit{Fin}}\left(168\right), \mathit{Int}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The leading block is the A229585 transfer matrix. The lower left block is zero. For a valid source boundary p and budget d, the entry at source cl(p,d) and exhausted destination 72 plus j counts next rows of exact cost d whose exhausted class is j. For k in Fin 16, the upper-right source row zeroBudgetClass(k) uses columns 16 through 71 of A229585.T at source Fin.castAdd(56,k), followed by 40 zeros. The remaining 56 active words are selected by the source's rank in the increasing complement of zeroBudgetClass. For an active packed word, an exitRead value below 72 selects the entry at its index in the old leading row. The weight takes Int.toNat of that entry and casts it back to Int. An exitRead value at least 72 selects the digit at position exitRead minus 72 in the source word, starting with the least significant digit, and casts that digit to Int. Within the lower right block, the original exhausted sources reuse the exhausted rows and columns of A229585, followed by 40 zeros. The 40 new exhausted rows select from 38 distinct packed words. They return zero for exitRead values below 72 and cast the selected radix-16 digit to Int otherwise.

**Theorem 1.5 (Multiplicity of a successor class).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\forall s: \operatorname{\mathit{Fin}}\left(168\right), ((\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \implies (\sum_{r: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le d) \land (\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), d - (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = s)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(p, d\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Every next row whose cost fits the available budget contributes one to its destination.

The exact-cost check tries each colour at a cell and subtracts its matches with the previous colour and the optional boundary colour. It discards a choice when its cost exceeds the remaining budget and accepts a final colour only when it spends the entire remainder. It accumulates the surviving rows as radix-three codes and counts their exhausted classes.

At budget zero every leading destination has multiplicity zero. The literal counts require a strictly positive residual budget for a leading destination, and the transfer uses the zero lower-left block.

A separate candidate is that the source is valid if and only if the two rows agree at every destination. Exhaustive integer comparisons give the converse at budgets zero through two. At budget three the literal row has total at least 810, compared with a maximum matrix row total of 426, and the literal total is nondecreasing. The converse still lacks a Lean proof.

**Definition 1.6 (Reindex an inherited exhausted class).**

$$\forall i: \operatorname{\mathit{Fin}}\left(72\right), (\operatorname{\mathit{oldZeroImage}}\left(i\right) = (\operatorname{\mathit{if}} h: (16 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(40, \operatorname{\mathit{Fin}}.\operatorname{\mathit{subNat}}\left(16, i, h\right)\right) \operatorname{\mathit{else}} 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.oldZeroImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Subtract 16 below the embedding into Fin 96. The index is zero when the input is below 16.

**Theorem 1.7 (Source validity).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{Valid}}\left(p, d\right) \Leftrightarrow (d \le 2) \land (\operatorname{\mathit{HardinA229635State}}.\operatorname{h}\left(p\right) \le 2 - d)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.valid_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Validity bounds the remaining budget and the number of equal neighbours in the boundary.

**Theorem 1.8 (New class under relabelling).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{fresh}}\left((\lambda i \mapsto e\left(p\left(i\right)\right))\right) = \operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{fresh}}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.fresh_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Permuting colours preserves the equality pattern.

**Theorem 1.9 (Exhausted class under relabelling).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\operatorname{\mathit{exhaustedClass}}\left((\lambda i \mapsto e\left(p\left(i\right)\right))\right) = \operatorname{\mathit{exhaustedClass}}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The exhausted index depends on the equality pattern.

**Theorem 1.10 (Successor in the leading block).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\forall c: \mathit{Nat}, (\forall j: \operatorname{\mathit{Fin}}\left(72\right), ((c \le d) \land (\operatorname{\mathit{cl}}\left(p, d - c\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(96, j\right)) \Leftrightarrow (0 < d) \land ((c \le d - 1) \land (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1 - c\right) = j))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.active_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A leading destination occurs with strictly positive budget after the transition.

**Theorem 1.11 (Successor in the exhausted block).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\forall c: \mathit{Nat}, (\forall j: \operatorname{\mathit{Fin}}\left(96\right), ((c \le d) \land (\operatorname{\mathit{cl}}\left(p, d - c\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, j\right)) \Leftrightarrow (c = d) \land (\operatorname{\mathit{exhaustedClass}}\left(p\right) = j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

An exhausted destination occurs when the cost equals the remaining budget.

**Theorem 1.12 (Horizontal charge of a new head).**

$$\forall x: \operatorname{\mathit{Fin}}\left(3\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(x, p\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(x, p\right)\right) = (\operatorname{\mathit{if}} (x = p\left(0\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + \operatorname{\mathit{HardinA229635State}}.\operatorname{h}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.horizontal_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Prepending a colour adds one comparison with the first boundary cell.

**Theorem 1.13 (The copied exhausted columns).**

$$\forall j: \operatorname{\mathit{Fin}}\left(96\right), (\forall h: \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{exitRead}}\left(j\right)\right) < 72, (\forall i: \operatorname{\mathit{Fin}}\left(168\right), (\operatorname{T}\left(i, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, j\right)\right) = \operatorname{T}\left(i, \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(96, (\langle\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{exitRead}}\left(j\right)\right), h\rangle : \operatorname{\mathit{Fin}}\left(72\right))\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.copied_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A readout below 72 gives the corresponding frozen leading column with a zero suffix.

**Theorem 1.14 (Columns with the same new readout).**

$$\forall j: \operatorname{\mathit{Fin}}\left(96\right), (\forall k: \operatorname{\mathit{Fin}}\left(96\right), ((72 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{exitRead}}\left(j\right)\right)) \implies ((\operatorname{\mathit{exitRead}}\left(j\right) = \operatorname{\mathit{exitRead}}\left(k\right)) \implies (\forall i: \operatorname{\mathit{Fin}}\left(168\right), (\operatorname{T}\left(i, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, j\right)\right) = \operatorname{T}\left(i, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, k\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.new_column_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A readout at least 72 determines the entire exhausted destination column.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.active_cut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.copied_column`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhaustedClass`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_cut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exitRead`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.fresh_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.horizontal_cons`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.new_column_congr`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.oldZeroImage`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.valid_parts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column](../../../../Combinatorics/TraceAvoidingArrays/HardinA233154Column.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows](../../../../Combinatorics/TraceAvoidingArrays/HardinA233154Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws](../../CrossedStripDefectsWide/P5b/HardinA229635Laws.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State](../../CrossedStripDefectsWide/P5b/HardinA229635State.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../../StripDefects/HardinA229637RowColumn.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip](../HardinA229585Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](../HardinA229585StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitTable](../HardinA229585StripOrbitTable.md)
