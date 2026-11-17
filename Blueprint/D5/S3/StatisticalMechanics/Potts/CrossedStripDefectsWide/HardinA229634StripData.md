# Width-five two-defect transfer

## Abstract

Exact-budget HDA extension.

**Definition 1.1 (Residual-budget invariant).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right) = ((d \le 2) \land (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 2 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The row and natural residual budget satisfy d at most two and horizontal defects at most two minus d; subtraction is truncated natural subtraction.

**Definition 1.2 (Class map).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}: \left(\operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right)\right) \to \left(\operatorname{\mathit{Nat}} \to \operatorname{\mathit{Fin}}\left(33\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The function retains HardinA229531StripData.cl at positive residual budget, subtracts one from the budget and embeds Fin 20 into Fin 33. At zero residual it appends thirteen classes: six proper classes followed by seven classes of identical zero-cost successor counts. The equality code sums powers of two for the ten equal-position predicates. Membership in each finite code set selects a class. Nat.mod denotes the nonnegative remainder modulo six. HardinA229634StripClasses.transition_counts pins every class against actual rows.

**Definition 1.3 (Block extension).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(33\right), \operatorname{\mathit{Fin}}\left(33\right), \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The 33 by 33 integer matrix is reindexed from a 20 plus 13 block matrix. Its upper left block is exactly HardinA229531StripData.T and its lower left block is zero. The six proper rows of the new lower right block use the frozen terminal proper block at indices six through eleven. All appended entries are pinned by HardinA229634StripClasses.transition_counts.

**Definition 1.4 (Initial distribution).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(33\right) \to \operatorname{\mathit{Int}})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

Fin.append retains HardinA229531StripData.initial and appends thirteen weights counting initial rows with two horizontal defects. The literal initial-row sum is checked in HardinA229634Strip.finite_certificate.

**Definition 1.5 (Terminal indicator).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{terminal}}: \operatorname{\mathit{Fin}}\left(33\right) \to \operatorname{\mathit{Int}})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The first twenty entries are zero and the appended thirteen entries are one. The finite certificate identifies this with zero residual budget for every valid row.

**Definition 1.6 (Forward vectors).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(21\right) \to \left(\operatorname{\mathit{Fin}}\left(33\right) \to \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The 21 by 33 integer table keeps all fourteen available forward rows from HardinA229531StripData.W in the inherited block. The remaining entries are explicit integers. HardinA229634Strip.finite_certificate pins row zero to initial, all twenty matrix steps, and the order-eighteen relation at row twenty.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.terminal`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData](../CrossedStripDefects/HardinA229531StripData.md)
