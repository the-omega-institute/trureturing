# Horizontal Saturation Separation

## Abstract

A larger sensor budget can repair one family, while a saturated language may fail.

**Definition 1.1 (Typed interface family).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.InterfaceFamily`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.InterfaceFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An InterfaceFamily assigns a possibly dependent observation type and readout to each sensor index.

**Definition 1.2 (Union of all interfaces).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.interfaceUnion`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.interfaceUnion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full union is the canonical dependent jointReadout of every sensor.

**Definition 1.3 (Union of a selected subfamily).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.subfamilyUnion`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.subfamilyUnion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A selected subset is represented by its subtype and joined with the same canonical jointReadout.

**Definition 1.4 (Repairable budget insufficiency).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.BudgetInsufficient`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.BudgetInsufficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The current subfamily is inadequate, but a strict expansion drawn from the already available sensor family is adequate.

**Definition 1.5 (Saturated observation-language insufficiency).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.ObservationLanguageInsufficient`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.ObservationLanguageInsufficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation language is insufficient when its full interface union cannot recover the target.

**Definition 1.6 (Completion by a new semantic coordinate).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.semanticCompletion`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.semanticCompletion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Semantic completion joins the saturated old profile with the target as a new coordinate.

**Theorem 1.7 (Semantic completion preserves the family and recovers the target).**

$$\forall q, T, \operatorname{Refines}\left(\operatorname{interfaceUnion}\left(q\right), \operatorname{semanticCompletion}\left(q, T\right)\right) \land \operatorname{TargetAdequate}\left(\operatorname{semanticCompletion}\left(q, T\right), T\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.semantic_completion_preserves_family_and_recovers_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical concept join projects to the entire old sensor profile and to the newly added target coordinate.

**Theorem 1.8 (Semantic completion is the least common refinement).**

$$\forall q, T, C, \operatorname{Refines}\left(\operatorname{interfaceUnion}\left(q\right), C\right) \land \operatorname{TargetAdequate}\left(C, T\right) \Rightarrow \operatorname{Refines}\left(\operatorname{semanticCompletion}\left(q, T\right), C\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.semantic_completion_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every candidate exposing both the old interface union and the target also exposes their semantic completion.

**Definition 1.9 (Budget-insufficiency sensor witness).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.budgetSensorFamily`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.budgetSensorFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean witness family contains a constant sensor and an identity sensor with the same output type.

**Definition 1.10 (Observation-language witness).**

Lean statement: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.constantSensorFamily`

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.constantSensorFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The language-insufficiency witness has one constant sensor on Boolean states.

**Theorem 1.11 (Semantic minimality needs visibility of the old family).**

$$\operatorname{TargetAdequate}\left(constUnit, constUnit\right) \land \neg \operatorname{Refines}\left(\operatorname{semanticCompletion}\left(budgetSensorFamily, constUnit\right), constUnit\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.family_visibility_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant candidate recovers a constant target, but it cannot recover the completion of the Boolean budget family. Thus family visibility cannot be dropped from semantic minimality.

**Theorem 1.12 (Semantic minimality needs visibility of the target).**

$$\operatorname{Refines}\left(\operatorname{interfaceUnion}\left(constantSensorFamily\right), \operatorname{interfaceUnion}\left(constantSensorFamily\right)\right) \land \neg \operatorname{Refines}\left(\operatorname{semanticCompletion}\left(constantSensorFamily, booleanTarget\right), \operatorname{interfaceUnion}\left(constantSensorFamily\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.target_visibility_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full constant family recovers itself, but it cannot recover a completion carrying the Boolean target. Thus target visibility cannot be dropped from semantic minimality.

**Theorem 1.13 (Adding an available sensor repairs a deficient budget).**

$$\operatorname{BudgetInsufficient}\left(budgetSensorFamily, booleanTarget, \{false\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.budget_insufficiency_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected constant sensor cannot recover Boolean identity. Strictly expanding to the full family adds the existing identity sensor and provides an exact decoder.

**Theorem 1.14 (No subfamily or repeated transcript repairs a constant language).**

$$\begin{aligned}\operatorname{ObservationLanguageInsufficient}\left(constantSensorFamily, booleanTarget\right) \land\\(\forall J\subseteq Unit, \neg \operatorname{TargetAdequate}\left(\operatorname{subfamilyUnion}\left(constantSensorFamily, J\right), booleanTarget\right)) \land\\\forall n\in\mathbb{N}, \operatorname{KernelFactorsThrough}\left(\operatorname{interfaceUnion}\left(constantSensorFamily\right), \operatorname{iidRepetition}\left(n, constantBooleanTranscriptKernel\right)\right) \land\\\neg \operatorname{IdentifiesTarget}\left(\operatorname{iidRepetition}\left(n, constantBooleanTranscriptKernel\right), booleanTarget\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.observation_language_insufficiency_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full constant family is inadequate, so the imported subfamily persistence theorem rules out every selected subset.

Its transcript kernel factors through the same full union after every iid repetition, including zero samples. The imported kernel barrier therefore keeps the Boolean target unidentified.

**Theorem 1.15 (Budget insufficiency does not imply language insufficiency).**

$$\neg (\operatorname{BudgetInsufficient}\left(budgetSensorFamily, booleanTarget, \{false\}\right) \Rightarrow \operatorname{ObservationLanguageInsufficient}\left(budgetSensorFamily, booleanTarget\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.budget_insufficiency_does_not_imply_observation_language_insufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named budget witness is repairable by an existing sensor, and its full family already recovers the target. It therefore witnesses the formal nonimplication between the two notions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.BudgetInsufficient`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.InterfaceFamily`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.ObservationLanguageInsufficient`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.budgetSensorFamily`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.budget_insufficiency_does_not_imply_observation_language_insufficiency`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.budget_insufficiency_witness`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.constantSensorFamily`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.family_visibility_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.interfaceUnion`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.observation_language_insufficiency_witness`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.semanticCompletion`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.semantic_completion_minimal`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.semantic_completion_preserves_family_and_recovers_target`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.subfamilyUnion`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation.target_visibility_is_necessary`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyInadequacyPersistence](SubfamilyInadequacyPersistence.md)
- Dependency: [D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier](../../Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier.md)
