# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Theorem 1.1 (steps).**

$$\forall i: \operatorname{\mathit{Fin}}\left(12\right), (\forall s: \operatorname{\mathit{Fin}}\left(32\right), (\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(13 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right) + 1\right): \operatorname{\mathit{Fin}}\left(26\right)), \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, s\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229457StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(13 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right): \operatorname{\mathit{Fin}}\left(26\right))\right), \operatorname{\mathit{HardinA229457StripData}}.\operatorname{T}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, s\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripStep1.steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

Each equality certifies one of the 32 one-defect coordinates of the forward row vector multiplied by the transfer matrix. The ten zero-defect coordinates come from the normalized A233127 continuation powers. The finite index has its displayed natural value.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripStep1.steps`
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
