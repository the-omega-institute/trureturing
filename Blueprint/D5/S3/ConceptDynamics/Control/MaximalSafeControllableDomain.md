# Maximal Safe Controllable Domain

## Abstract

The semantic indefinitely safe domain is the greatest controlled-safe fixed point.

**Theorem 1.1 (The indefinitely safe domain is the greatest fixed point).**

$$\forall X \in Type,\; \forall system \in \operatorname{ControlSystem}\left(X\right), S \in \operatorname{Set}\left(X\right),\; \operatorname{let} F : \operatorname{OrderHom}\left(\operatorname{Set}\left(X\right), \operatorname{Set}\left(X\right)\right) := K \mapsto \operatorname{intersect}\left(S, \operatorname{CPre}\left(system, K\right)\right);\\{}\operatorname{let} Kstar : \operatorname{Set}\left(X\right) := \{x \in X \mid \exists I \in \operatorname{Set}\left(X\right),\; x \in I \land \left(I \subseteq S \land \left(\forall y \in I,\; \exists u \in \operatorname{Action}\left(system, y\right),\; \operatorname{successor}\left(system, y, u\right) \subseteq I\right)\right)\};\\{}Kstar = \operatorname{gfp}\left(F\right) \land \left(\left(\forall x \in \operatorname{gfp}\left(F\right),\; \exists u \in \operatorname{Action}\left(system, x\right),\; \operatorname{successor}\left(system, x, u\right) \subseteq \operatorname{gfp}\left(F\right)\right) \land \left(\operatorname{gfp}\left(F\right) \subseteq Kstar \land Kstar \subseteq \operatorname{gfp}\left(F\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/MaximalSafeControllableDomain.maximal_safe_controllable_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A control system supplies a state-dependent action type and a nonempty successor set for every available action. The controlled predecessor uses existential action choice and universal successor containment.

The indefinitely safe set is constructed semantically: a state must lie in some subset of the safe states that offers a confining action at each of its states. It is not defined as a fixed point.

Independently, the displayed monotone operator intersects the safe set with the canonical controlled predecessor. Knaster-Tarski identifies its greatest fixed point with the semantic indefinitely safe set.

The remaining public clauses expose the confining action, indefinite-safety inclusion, and converse maximality. Repository searches found no exact theorem; Mathlib's greatest-fixed-point laws are applied directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/MaximalSafeControllableDomain.maximal_safe_controllable_domain`
- Dependency: [D5/S3/ConceptDynamics/Control/FiniteHorizonReachability](FiniteHorizonReachability.md)
