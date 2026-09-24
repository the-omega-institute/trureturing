# Three coefficient-code cuts

## Abstract

Three indexed readings of signed coefficient codes.

**Definition 1.1 (coefficientSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate.coefficientSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate.coefficientSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature has three CUT indices, each returning a code in Fin(9), and no anchors. Codes can represent real coefficients from -4 through 4 by subtracting four.

**Definition 1.2 (coefficientRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate.coefficientRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate.coefficientRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplied coefficient reader is evaluated at the state and the selected index. Its full word is available through the three readings; no proposition or theorem is stored in the reader.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate.coefficientRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate.coefficientSignature`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](TheoremUnit.md)
- Dependency: [D5/S3/ConceptDynamics/RegistrationWitnesses](../RegistrationWitnesses.md)
