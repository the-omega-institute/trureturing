# Plan-Cylinder Commitment Telescoping

## Abstract

Action-selected finite plan cylinders telescope their commitment depths.

**Theorem 1.1 (Plan-cylinder commitment depth telescopes).**

$$\forall History \in \operatorname{Type}, Plan \in \operatorname{Type}, Action \in \operatorname{Type}, Omega \in History \to \operatorname{Finset}\left(Plan\right), prescribes \in History \to \left(Plan \to Action\right), history \in Nat \to History, action \in Nat \to Action, n \in Nat,\; \left([\operatorname{DecidableEq}\left(Action\right)] \land \left(\left(\forall h \in History,\; Omega\left(h\right) \neq \emptyset\right) \land \left(\forall t \in Nat,\; t < n \Rightarrow Omega\left(history\left(t + 1\right)\right) = \{omega \in Omega\left(history\left(t\right)\right) \mid prescribes\left(history\left(t\right), omega\right) = action\left(t\right)\}\right)\right)\right) \Rightarrow \sum_{t \in \operatorname{range}\left(n\right)} {\operatorname{log2}\left(\operatorname{card}\left(Omega\left(history\left(t\right)\right)\right)\right) - \operatorname{log2}\left(\operatorname{card}\left(\{omega \in Omega\left(history\left(t\right)\right) \mid prescribes\left(history\left(t\right), omega\right) = action\left(t\right)\}\right)\right)} = \operatorname{log2}\left(\operatorname{card}\left(Omega\left(history\left(0\right)\right)\right)\right) - \operatorname{log2}\left(\operatorname{card}\left(Omega\left(history\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/PlanCylinderCommitmentTelescoping.plan_cylinder_commitment_depth_telescopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each history carries a finite nonempty set of compatible complete future plans. A plan cylinder retains exactly those plans whose current prescription equals the action actually selected.

When every next history has exactly the selected cylinder as its compatible-plan set, the stepwise base-two log-cardinality losses cancel to the initial-minus-terminal loss.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/PlanCylinderCommitmentTelescoping.plan_cylinder_commitment_depth_telescopes`
