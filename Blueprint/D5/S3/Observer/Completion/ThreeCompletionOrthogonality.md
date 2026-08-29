# Three Completion Tasks

## Abstract

Identity, representative normalization, and future behavior are distinct completion tasks, with one same-readout implication recorded honestly.

**Theorem 1.1 (Prime valuations can identify an ideal without a global generator).**

$$\operatorname{DedekindDomain}(R) \land \operatorname{Nontrivial}(\operatorname{ClassGroup}(R)) \Rightarrow\\\exists I: \operatorname{Ideal}(R), \operatorname{PrimeValuationIdentityCompletion}(I) \land \neg \operatorname{IsPrincipal}(I) \land \neg \operatorname{UniqueGenerator}(I).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.prime_valuation_identity_without_global_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a Dedekind domain with nontrivial class group, the imported prime valuation faithfulness theorem identifies a nonzero ideal supplied by the class group, while nonprincipality excludes every generator.

**Theorem 1.2 (A PID has no valuation-identified nonprincipal witness).**

$$\neg \exists I: \operatorname{Ideal}(\mathbb{Z}), \operatorname{PrimeValuationIdentityCompletion}(I) \land \neg \operatorname{IsPrincipal}(I).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.nontrivial_class_group_is_necessary_for_valuation_generator_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ideal of the integers is principal. This concrete counterexample shows why the nontrivial-class-group premise is necessary for the first strictness witness.

**Theorem 1.3 (Class-group principality does not choose a unique generator).**

$$\exists I: \operatorname{Ideal}(\mathbb{Z}), \operatorname{ClassGroupPrincipalityDecision}(I) \land \operatorname{IsPrincipal}(I) \land \neg \operatorname{UniqueGenerator}(I).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.class_group_principality_without_unique_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported integer witnesses one and minus one generate the same nonzero principal ideal. The class-group criterion decides principality, but the ideal equation has more than one generator.

**Theorem 1.4 (A closed behavior quotient can merge microscopic identities).**

$$\forall n\in \mathbb{N}, \operatorname{FactorsThrough}(qBool, \operatorname{iidTranscript}(n)) \land\\\operatorname{BehaviorCompletion}(qBool, \operatorname{iidTranscript}(n)) \land\\\exists x, y\in Bool, x \neq y \land \operatorname{ker}(qBool, x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.future_behavior_quotient_merges_micro_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite repetition count, including zero, the constant Boolean transcript law factors through the one-point interface. False and true remain distinct states in the same Setoid.ker fiber.

**Theorem 1.5 (Identity completion does not imply normalization completion).**

$$\operatorname{IdentityCompletion}(idBool) \land \neg \operatorname{NormalizationCompletion}(trueBoolRelation).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.identity_completion_does_not_imply_normalization_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity readout separates Boolean states, while the indiscriminate Boolean representative relation has two representatives per object.

**Theorem 1.6 (Normalization completion does not imply identity completion).**

$$\operatorname{NormalizationCompletion}(equalityBoolRelation) \land \neg \operatorname{IdentityCompletion}(constantBoolInterface).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.normalization_completion_does_not_imply_identity_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality chooses one Boolean representative for each object, while the constant interface still merges false and true.

**Theorem 1.7 (Normalization completion does not imply behavior completion).**

$$\operatorname{NormalizationCompletion}(equalityBoolRelation) \land \neg \operatorname{BehaviorCompletion}(constantBoolInterface, identityBoolFuture).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.normalization_completion_does_not_imply_behavior_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unique equality representatives coexist with a constant readout and an identity-valued future that differs inside its fiber.

**Theorem 1.8 (Behavior completion does not imply identity completion).**

$$\operatorname{BehaviorCompletion}(constantBoolInterface, constantFuture) \land \neg \operatorname{IdentityCompletion}(constantBoolInterface).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.behavior_completion_does_not_imply_identity_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant future is closed on the constant Boolean interface, but that interface does not identify its two microscopic states.

**Theorem 1.9 (Behavior completion does not imply normalization completion).**

$$\operatorname{BehaviorCompletion}(constantBoolInterface, constantFuture) \land \neg \operatorname{NormalizationCompletion}(trueBoolRelation).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.behavior_completion_does_not_imply_normalization_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constant Boolean behavior closes, while an indiscriminate representative relation still fails uniqueness.

**Theorem 1.10 (Identity under one readout implies every deterministic behavior).**

$$\forall q, f, \operatorname{IdentityCompletion}(q) \Rightarrow \operatorname{BehaviorCompletion}(q, f).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.same_readout_identity_implies_behavior_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sixth requested nonimplication direction is false under the formalized same-readout semantics: injectivity turns equal readouts into equal states, so every deterministic future is fiber-constant.

## References

- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.behavior_completion_does_not_imply_identity_completion`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.behavior_completion_does_not_imply_normalization_completion`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.class_group_principality_without_unique_generator`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.future_behavior_quotient_merges_micro_identity`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.identity_completion_does_not_imply_normalization_completion`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.nontrivial_class_group_is_necessary_for_valuation_generator_gap`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.normalization_completion_does_not_imply_behavior_completion`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.normalization_completion_does_not_imply_identity_completion`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.prime_valuation_identity_without_global_generator`
- Truth anchor: `D5/S3/Observer/Completion/ThreeCompletionOrthogonality.same_readout_identity_implies_behavior_completion`
- Dependency: [D5/S3/Factorization/Embeddings/DirichletUnitCompletion](../../Factorization/Embeddings/DirichletUnitCompletion.md)
- Dependency: [D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers](../../Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers.md)
- Dependency: [D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness](../../Factorization/IdealClassGroups/LocalPrincipalityBlindness.md)
- Dependency: [D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier](../MeasureSeparation/FactorizedTranscriptKernelBarrier.md)
