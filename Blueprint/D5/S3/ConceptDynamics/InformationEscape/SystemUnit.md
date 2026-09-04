# Boolean Pair System Unit

## Abstract

Two Boolean coordinate CUTs give a concrete irredundant system unit.

**Definition 1.1 (Boolean-pair primitive signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature contains two CUT slots and an empty anchor family.

**Definition 1.2 (Boolean-pair primitive-law arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena has four states and two CUT slots, with no anchor slots.

**Definition 1.3 (Coordinate projection realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two primitive readouts are the first and second Boolean projections.

**Definition 1.4 (Concrete system-unit statement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.BoolPairFstSndStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.BoolPairFstSndStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The statement combines discrete joint agreement, positive empty-catalog capture, and the prescribed private pair.

**Theorem 1.5 (The coordinate system unit is irredundant).**

$$BoolPairFstSndStatement.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.bool_pair_fst_snd_catalog_irredundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite kernel evaluation proves discrete agreement, positive capture against the empty leave-one-out family, and separation of 00 from 10.

**Theorem 1.6 (System-unit realization certificate).**

$$LegacyPrimitiveRealization\left(boolPairFstSndArena, BoolPairFstSndStatement, boolPairFstSndRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.bool_pair_fst_snd_catalog_irredundant_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete system theorem uses the same legacy-realization interface as the ten frozen applications.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.BoolPairFstSndStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.boolPairFstSndSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.bool_pair_fst_snd_catalog_irredundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/SystemUnit.bool_pair_fst_snd_catalog_irredundant_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty](StructuralNovelty.md)
