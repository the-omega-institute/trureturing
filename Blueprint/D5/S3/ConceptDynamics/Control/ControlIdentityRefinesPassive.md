# Control Identity Refines Passive Identity

## Abstract

Adding control actions refines action-induced identity, while passive identity need not recover the full control identity.

**Theorem 1.1 (Control identity refines passive identity).**

$$\forall A, X, Y: Type, P, C: \operatorname{Set}\left(A\right),\\{}act: A \to X \to X, obs: X \to Y,\\{}P \subseteq C \Rightarrow \operatorname{Refines}\left(I_{P}, I_{C}\right) \land \sim_{C} \subseteq \sim_{P}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/ControlIdentityRefinesPassive.control_identity_refines_passive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action identity of a state is the complete family of observed outcomes obtained after applying every action in the chosen set. When every passive action is also a control action, restricting that family from control coordinates to passive coordinates provides the required factor map.

Thus the full-control identity refines the passive identity. Equally, states that agree after every control action must agree after every passive action, so control indistinguishability is contained in passive indistinguishability.

**Lemma 1.2 (Passive identity need not recover control identity).**

$$A = X = Y = Bool, P = \{{false}\}, C = \{{false}, {true}\},\\{}act(a, x) = \operatorname{ite}\left(a, x, false\right), obs = id,\\{}\Rightarrow P \subseteq C \land \operatorname{Refines}\left(I_{P}, I_{C}\right) \land \neg \operatorname{Refines}\left(I_{C}, I_{P}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/ControlIdentityRefinesPassive.reverse_control_refinement_can_fail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the two-state Boolean system, the sole passive action resets every state to false, whereas the additional control action preserves the state. The passive readout therefore identifies false and true, but the control readout separates them. Forward refinement still holds, while no factor map can reconstruct the control identity from the passive one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/ControlIdentityRefinesPassive.control_identity_refines_passive`
- Truth anchor: `D5/S3/ConceptDynamics/Control/ControlIdentityRefinesPassive.reverse_control_refinement_can_fail`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability](../OperationalOntology/ActionExpansionIndistinguishability.md)
