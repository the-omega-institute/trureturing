# Semantics

## Abstract

Licensed Foundation.Logic.Semantics source for the concrete first-order pair extension.

Source-command excerpt selected within Foundation.Logic.Semantics, lines 1-363, at Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. The optional Semantics.Top (Set M) instance command at upstream line 251 is omitted. All other selected mathematical commands and their proofs retain the upstream source.

The Lean file retains selected upstream commands and their compiler companions. The immutable source map, modification notices, full Apache-2.0 license and retirement condition are in Library/ConceptDynamics/foundation2026firstorder.md.

**Remark 1.1 (Satisfaction by a set of models).**

Lean statement: `D5/S3/ConceptDynamics/ZfcLogic/Semantics.set_models_iff`

*Formalization.* `D5/S3/ConceptDynamics/ZfcLogic/Semantics.set_models_iff` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

A set satisfies a formula exactly when each of its members satisfies that formula.

**Remark 1.2 (Meaningful sets of models).**

Lean statement: `D5/S3/ConceptDynamics/ZfcLogic/Semantics.set_meaningful_iff_nonempty`

*Formalization.* `D5/S3/ConceptDynamics/ZfcLogic/Semantics.set_meaningful_iff_nonempty` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Assuming every individual model is meaningful, a set of models is meaningful exactly when it is nonempty. The original proof uses set_models_iff to normalize satisfaction.

**Remark 1.3 (Satisfiability and meaningful model classes).**

Lean statement: `D5/S3/ConceptDynamics/ZfcLogic/Semantics.meaningful_iff_satisfiableSet`

*Formalization.* `D5/S3/ConceptDynamics/ZfcLogic/Semantics.meaningful_iff_satisfiableSet` (`✓ std3`).

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Under the same individual-model assumption, a theory is satisfiable exactly when its set of models is meaningful.

This excerpt supplies semantic interfaces and proofs for downstream first-order developments. It does not represent the full upstream module or establish the complete CSA definition-elimination claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcLogic/Semantics.meaningful_iff_satisfiableSet`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcLogic/Semantics.set_meaningful_iff_nonempty`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcLogic/Semantics.set_models_iff`
- Dependency: [D5/S3/ConceptDynamics/ZfcFiniteCollections/List](../ZfcFiniteCollections/List.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcLanguageSupport/NotationClass](../ZfcLanguageSupport/NotationClass.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcLogic/LogicSymbolTwo](LogicSymbolTwo.md)
