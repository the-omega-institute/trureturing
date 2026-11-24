# The width-seven two-defect recurrence

## Abstract

The width-seven two-defect recurrence.

**Definition 1.1 (First-row weights).**

$$\operatorname{\mathit{HardinA229693Strip}}.\operatorname{\mathit{initial}} = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{initial}}, \lambda i: \operatorname{\mathit{Fin}}\left(96\right) \mapsto ((\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right) < 56) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (\exists k: \operatorname{\mathit{Fin}}\left(16\right), (i = \operatorname{\mathit{oldZeroImage}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{zeroBudgetClass}}\left(k\right)\right))) \operatorname{\mathit{then}} (0: \mathit{Int}) \operatorname{\mathit{else}} (6: \mathit{Int})) \operatorname{\mathit{else}} (12: \mathit{Int})))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The first 72 entries are the A229585 initial weights. The remaining entries count labelled rows with exactly two horizontal defects, grouped by exhausted boundary class. The strip counting formula uses this vector on the left.

**Definition 1.2 (Acceptance weights).**

$$\operatorname{\mathit{HardinA229693Strip}}.\operatorname{\mathit{terminal}} = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(0 : (\operatorname{\mathit{Fin}}\left(72\right)) \to (\mathit{Int}), 1 : (\operatorname{\mathit{Fin}}\left(96\right)) \to (\mathit{Int})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A completed strip is accepted when its remaining budget is zero.

**Theorem 1.3 (The labelled strip count).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{literalCount}}\left((q := 3), \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{antidiagonal}}, 2, n + 1\right): \mathit{Int}) = \operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA229693Strip}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left((\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T})^{n}, \operatorname{\mathit{HardinA229693Strip}}.\operatorname{\mathit{terminal}}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The first row contributes the initial weight. Each later row multiplies by the transfer matrix, and terminal weights require exact exhaustion. The empty strip has zero colourings with exactly two defects, whereas the zero-power matrix coefficient counts the positive number of qualifying one-row strips.

**Definition 1.4 (Literal array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda f: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(7\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(7\right) \mapsto (f\left((i, j)\right)))\right)\right) = 2) \land (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{\mathit{Normal}}\left(f\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The finite filter ranges over all three-colour arrays. The condition inherited from A229585 orders colour introductions by row and then by column.

**Theorem 1.5 (Integer recurrence).**

$$\forall t: \mathit{Nat}, ((\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 15\right): \mathit{Int}) = 126 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 14\right): \mathit{Int}) - 6345 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 13\right): \mathit{Int}) + 165456 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 12\right): \mathit{Int}) - 2474469 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 11\right): \mathit{Int}) + 22918302 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 10\right): \mathit{Int}) - 138045627 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 9\right): \mathit{Int}) + 554666940 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 8\right): \mathit{Int}) - 1494608922 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 7\right): \mathit{Int}) + 2659094568 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 6\right): \mathit{Int}) - 2986698420 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 5\right): \mathit{Int}) + 1913187600 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 4\right): \mathit{Int}) - 531441000 \cdot (\operatorname{\mathit{HardinA229693Strip}}.\operatorname{a}\left(t + 3\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

All array counts in this equality are cast to integers. At least two colours occur in a nonempty array with two monochromatic bonds. Relabelling gives six labelled arrays per canonical array. The vector identity for the transfer at fourteen steps propagates to later steps by right multiplication.

For every table p of fifteen integer row vectors indexed by Fin 168, assume that p at zero is the initial vector and that for every j in Fin 14, the row at j.succ is the product of the row at j.castSucc with T. Induction then identifies the row at every i in Fin 15 with forward iteration from the initial vector for i.val steps.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.count_transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws](../../CrossedStripDefectsWide/P5b/HardinA229635Laws.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts](../../CrossedStripDefectsWide/P5b/HardinA229635Starts.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State](../../CrossedStripDefectsWide/P5b/HardinA229635State.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../../StripDefects/HardinA229637RowColumn.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer](HardinA229693StripTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip](../HardinA229585Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](../HardinA229585StripData.md)
