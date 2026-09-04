# Local-Law Gluing Obstruction Realization

## Abstract

The three pulled-back pair laws realize a four-class gluing-obstruction kernel.

**Theorem 1.1 (Gluing realization equivalence).**

$$\operatorname{LegacyPrimitiveRealization}\left(localLawGluingArena, LocalLawGluingStatement, localLawGluingRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward and backward maps translate set-image fibers and coded admission without invoking the frozen theorem.

**Theorem 1.2 (Four kernel classes).**

$$\operatorname{card}\left(signatureClasses\right) = 4.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhaustive evaluation of the three ADMIT bits yields four signatures.

**Theorem 1.3 (Private pair separation).**

$$\operatorname{Not}\left(\operatorname{agrees}\left(localLawGluingRealization, stateZero, stateOne\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer admission test separates 000 from 001.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction](../InformationEscapeArenas/LocalLawGluingObstruction.md)
