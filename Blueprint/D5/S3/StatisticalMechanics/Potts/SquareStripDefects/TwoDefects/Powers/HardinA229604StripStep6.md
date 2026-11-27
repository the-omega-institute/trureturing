# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Theorem 1.1 (steps).**

$$\forall i: \operatorname{\mathit{Fin}}\left(6\right), (\forall s: \operatorname{\mathit{Fin}}\left(18\right), (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(12 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right) + 1\right): \operatorname{\mathit{Fin}}\left(25\right)), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(42 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right)\right): \operatorname{\mathit{Fin}}\left(96\right))\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(12 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right): \operatorname{\mathit{Fin}}\left(25\right))\right), \operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}, (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(42 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right)\right): \operatorname{\mathit{Fin}}\left(96\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep6.steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

These integer identities give six consecutive forward steps in 18 new terminal coordinates.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep6.steps`
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData](../../HardinA229604StripData.md)
