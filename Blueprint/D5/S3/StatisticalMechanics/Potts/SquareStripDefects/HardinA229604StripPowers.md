# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Theorem 1.1 (steps).**

$$(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(24\right), (\forall s: \operatorname{\mathit{Fin}}\left(96\right), (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right), s\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229604StripData}}.\operatorname{T}, s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers.steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

Every one of the 24 forward steps holds in all 96 coordinates; the first 42 coordinates use the one-defect forward identities.

**Theorem 1.2 (relation).**

$$\forall s: \operatorname{\mathit{Fin}}\left(96\right), (\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left(24, s\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(21\right)} (![137388096, (-1718948736), 9979813584, (-35729023024), 88409012652, (-160604595216), 222060410955, (-239066083215), 203308881255, (-137758028106), 74677395474, (-32398609896), 11214272853, (-3076398702), 661896144, (-110021385), 13836015, (-1278486), 83214, (-3573), 90]\left(j\right) \cdot \operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(3 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(25\right)), s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers.relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

The order-21 polynomial annihilates the forward vector starting at index three. On the old 42 coordinates it follows from the order-fourteen polynomial by multiplication with its degree-seven factor; only the 54 new coordinates need finite arithmetic evaluation.

**Theorem 1.3 (initial relation).**

$$\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left(23\right), \operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{terminal}}\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(21\right)} (![137388096, (-1718948736), 9979813584, (-35729023024), 88409012652, (-160604595216), 222060410955, (-239066083215), 203308881255, (-137758028106), 74677395474, (-32398609896), 11214272853, (-3076398702), 661896144, (-110021385), 13836015, (-1278486), 83214, (-3573), 90]\left(j\right) \cdot \operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA229604StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(25\right))\right), \operatorname{\mathit{HardinA229604StripData}}.\operatorname{\mathit{terminal}}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers.initial_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229604: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229604>.

*Commentary.*

At the preceding index, the polynomial has zero scalar terminal readout. Together with the vector identity, this includes exactly the first claimed height 24.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers.initial_relation`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers.relation`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers.steps`
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripData](HardinA229457StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers](HardinA229457StripPowers.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripData](HardinA229604StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep0](TwoDefects/Powers/HardinA229604StripStep0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep1](TwoDefects/Powers/HardinA229604StripStep1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep10](TwoDefects/Powers/HardinA229604StripStep10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep11](TwoDefects/Powers/HardinA229604StripStep11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep2](TwoDefects/Powers/HardinA229604StripStep2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep3](TwoDefects/Powers/HardinA229604StripStep3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep4](TwoDefects/Powers/HardinA229604StripStep4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep5](TwoDefects/Powers/HardinA229604StripStep5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep6](TwoDefects/Powers/HardinA229604StripStep6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep7](TwoDefects/Powers/HardinA229604StripStep7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep8](TwoDefects/Powers/HardinA229604StripStep8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep9](TwoDefects/Powers/HardinA229604StripStep9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
