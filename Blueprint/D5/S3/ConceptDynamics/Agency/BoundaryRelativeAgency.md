# Boundary-Relative Agency

## Abstract

A past-choice-updated decision variable is internal or external relative to observer access.

**Theorem 1.1 (Observer access determines the control boundary).**

$$\forall H \in \operatorname{Type}, O \in \operatorname{Type}, C \in \operatorname{Type}, D \in \operatorname{Type}, A \in \operatorname{Type}, o \in H \to O, c \in H \to C, u \in C \to D, a \in H \to A,\; \operatorname{ControlPrinciple}\left(u \circ c, a\right) \Rightarrow \left(\left(\operatorname{ControlPrinciple}\left(o, u \circ c\right) \Rightarrow \operatorname{ControlPrinciple}\left(o, a\right)\right) \land \left(\forall x \in H, y \in H,\; o\left(x\right) = o\left(y\right) \Rightarrow \left(u\left(c\left(x\right)\right) \ne u\left(c\left(y\right)\right) \Rightarrow \left(a\left(x\right) \ne a\left(y\right) \Rightarrow \left(\operatorname{MoralLuckWitness}\left(o, u \circ c\right) \land \neg \operatorname{ControlPrinciple}\left(o, a\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/BoundaryRelativeAgency.boundary_relative_agency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The decision process is constructed by applying the update map to the recorded past choice. The displayed control premise says that this same decision process determines action.

When the observer interface recovers the decision process, composition recovers action from the observer interface as well. This is the internal-reason side of the boundary.

On the external side, one shared pair has equal observer readouts but different decision and action values. It witnesses observer inaccessibility and rules out descent of action to that boundary.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/BoundaryRelativeAgency.boundary_relative_agency`
- Dependency: [D5/S3/ConceptDynamics/MoralLuck/MoralLuckDescent](../MoralLuck/MoralLuckDescent.md)
