# Diagonal Escape Needs Type Extension

## Abstract

Six countermodels separate four closure notions, including degenerate carriers.

**Theorem 1.1 (Faithfulness does not equal representation surjectivity).**

$$\operatorname{StateFaithfulness}\left(idBool\right) \land \neg \operatorname{RepresentationSurjectivity}\left(constFalse\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.state_faithfulness_not_representation_surjectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use identity as the Boolean readout and the constant-false map as the representation. Identity distinguishes states, while true has no representing coordinate under the constant map.

**Theorem 1.2 (Effective descent does not equal state faithfulness).**

$$\operatorname{EffectiveDescent}\left(constFalse, idBool\right) \land \neg \operatorname{StateFaithfulness}\left(constFalse\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.effective_descent_not_state_faithfulness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant Boolean readout identifies false and true, so it is not faithful. Identity dynamics preserve its sole realized fiber and therefore descend effectively to the realized image.

**Theorem 1.3 (State faithfulness does not equal self-description closure).**

$$\operatorname{StateFaithfulness}\left(idBool\right) \land \neg \operatorname{SelfDescriptionClosure}\left(Bool\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.state_faithfulness_not_self_description_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean identity is injective. A surjective Boolean evaluator would, by Lawvere diagonalization, give Boolean negation a fixed point; case analysis refutes that fixed point.

**Theorem 1.4 (Effective descent does not equal representation surjectivity).**

$$\operatorname{EffectiveDescent}\left(idBool, idBool\right) \land \neg \operatorname{RepresentationSurjectivity}\left(constFalse\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.effective_descent_not_representation_surjectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity Boolean dynamics descend along identity readout. The separate constant-false representation still omits the true state, showing that dynamic closure does not supply representation coverage.

**Theorem 1.5 (Representation surjectivity does not equal self-description closure).**

$$\operatorname{RepresentationSurjectivity}\left(idBool\right) \land \neg \operatorname{SelfDescriptionClosure}\left(Bool\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.representation_surjectivity_not_self_description_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean identity represents both states, but the carrier cannot encode all four Boolean endomaps. The formal contradiction again uses the fixed-point consequence of a surjective evaluator.

**Theorem 1.6 (Effective descent does not equal self-description closure).**

$$\operatorname{EffectiveDescent}\left(idBool, notBool\right) \land \neg \operatorname{SelfDescriptionClosure}\left(Bool\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.effective_descent_not_self_description_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean negation descends along identity readout because every identity fiber is preserved. This does not create an internal enumeration of all Boolean endomaps.

**Theorem 1.7 (The empty carrier separates typed maps from self-description).**

$$\operatorname{StateFaithfulness}\left(idEmpty\right) \land \operatorname{RepresentationSurjectivity}\left(idEmpty\right) \land \operatorname{EffectiveDescent}\left(idEmpty, idEmpty\right) \land \neg \operatorname{SelfDescriptionClosure}\left(Empty\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.empty_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Empty, identity injectivity and surjectivity are vacuous and identity dynamics descend. Self-description fails because the unique empty endomap has no code in an empty code type.

**Theorem 1.8 (The singleton carrier satisfies all four notions).**

$$\operatorname{StateFaithfulness}\left(idUnit\right) \land \operatorname{RepresentationSurjectivity}\left(idUnit\right) \land \operatorname{EffectiveDescent}\left(idUnit, idUnit\right) \land \operatorname{SelfDescriptionClosure}\left(Unit\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.unit_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Unit, identity readout and representation satisfy their map laws, identity dynamics descend, and the constant evaluator represents the unique Unit endomap. No nonemptiness premise is assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.effective_descent_not_representation_surjectivity`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.effective_descent_not_self_description_closure`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.effective_descent_not_state_faithfulness`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.empty_degenerate_audit`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.representation_surjectivity_not_self_description_closure`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.state_faithfulness_not_representation_surjectivity`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.state_faithfulness_not_self_description_closure`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.unit_degenerate_audit`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](../Dialectics/DeterministicInterfaceEquivalence.md)
