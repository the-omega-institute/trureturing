# Local-Law Gluing Obstruction Realization

## Abstract

The three pulled-back pair laws realize a four-class gluing-obstruction kernel.

**Definition 1.1 (Concrete gluing realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.localLawGluingRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.localLawGluingRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The realization evaluates equality on the two adjacent pairs and inequality on the outer pair.

**Theorem 1.2 (Gluing realization equivalence).**

$$(Prod.snd '' sameLaw = Prod.fst '' sameLaw \land Prod.fst '' sameLaw = Prod.fst '' differentLaw \land Prod.snd '' sameLaw = Prod.snd '' differentLaw) \land \neg {\exists state: Bool \times Bool \times Bool, (state.1, state.2.1) \in sameLaw \land (state.2.1, state.2.2) \in sameLaw \land (state.1, state.2.2) \in differentLaw} \iff localLawGluingArena.Law localLawGluingRealization.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence translates the frozen set-image statement to the arena law without invoking the frozen theorem.

**Theorem 1.3 (Four kernel classes).**

$$(Finset.univ.image(\lambda state: Bool \times Bool \times Bool, (localLawGluingRealization.readout admit01 state, localLawGluingRealization.readout admit12 state, localLawGluingRealization.readout admit02 state))).card = 4.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhaustive evaluation of the concrete three-ADMIT image yields four signatures.

**Theorem 1.4 (Private pair separation).**

$$\neg {localLawGluingRealization.toPrimitiveBundle.agrees (false, false, false) (false, false, true)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled primitive bundle separates 000 from 001.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.localLawGluingRealization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction](../InformationEscapeArenas/LocalLawGluingObstruction.md)
