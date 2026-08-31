# Boundary-Relative Agency

## Abstract

Observer access and faithful decision control determine which side of the boundary carries action.

**Theorem 1.1 (Observer access determines the control boundary).**

$$\forall H \in \operatorname{Type}, O \in \operatorname{Type}, C \in \operatorname{Type}, D \in \operatorname{Type}, A \in \operatorname{Type}, o \in H \to O, c \in H \to C, u \in C \to D, a \in H \to A, k \in D \to A,\; a = k \circ u \circ c \Rightarrow \left(\left(\operatorname{ControlPrinciple}\left(o, u \circ c\right) \Rightarrow \operatorname{ControlPrinciple}\left(o, a\right)\right) \land \left(\operatorname{MoralLuckWitness}\left(o, u \circ c\right) \Rightarrow \left(\operatorname{Injective}\left(k\right) \Rightarrow \neg \operatorname{ControlPrinciple}\left(o, a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/BoundaryRelativeAgency.boundary_relative_agency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The decision process is constructed by applying the update map to the recorded past choice. The displayed equality makes the map from decision values to actions explicit.

When the observer interface recovers the decision process, composition recovers action from the observer interface as well. This is the internal-reason side of the boundary.

The external implication has its own premises: the observer hides two distinct decision values, and the decision-to-action map is injective. Observer-based action recovery would equate their controlled outputs, so injectivity would contradict the hidden decision witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/BoundaryRelativeAgency.boundary_relative_agency`
- Dependency: [D5/S3/ConceptDynamics/MoralLuck/MoralLuckDescent](../MoralLuck/MoralLuckDescent.md)
