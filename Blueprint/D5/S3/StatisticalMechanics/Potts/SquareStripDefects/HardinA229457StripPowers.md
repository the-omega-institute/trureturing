# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Theorem 1.1 (steps).**

$$(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229457StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(25\right), (\forall s: \operatorname{\mathit{Fin}}\left(42\right), (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right), s\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}, s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers.steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The leading ten coordinates follow from the A233127 continuation powers. The transfer has zero lower-left block, and its leading block satisfies 64 times initial i times ProperTransfer.T i j = initial j times the transposed A233127 transfer entry. Induction gives 64 to the power k times W k j = initial j times the A233127 continuation at k and class j+1, and proves the defining integer division exact. Only the 32 one-defect coordinates use the finite step certificates.

**Theorem 1.2 (relation).**

$$\forall s: \operatorname{\mathit{Fin}}\left(42\right), (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}\left(15, s\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(14\right)} (![(-266256), 2220864, (-8262712), 18139608, (-26188161), 26218062, (-18693789), 9593166, (-3537110), 924894, (-167163), 20016, (-1482), 60]\left(j\right) \cdot \operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(26\right)), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers.relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The order-fourteen polynomial annihilates every coordinate of the forward vector starting at row index one.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers.relation`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers.steps`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows](../../../Combinatorics/TraceAvoidingArrays/HardinA233127Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripStep0](HardinA229457StripStep0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripStep1](HardinA229457StripStep1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer](ProperTransfer.md)
