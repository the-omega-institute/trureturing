# Predictive Closure Does Not Imply Intervention Closure

## Abstract

A naturally descending update need not make every intervention descend.

**Theorem 1.1 (Predictive closure does not imply intervention closure).**

$$\exists q \in \operatorname{Fin}\left(3\right) \to Bool, F \in \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right), Fa \in Bool \to \left(\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)\right),\; Fa\left(false\right) = F \land \left(\operatorname{EffectiveDescent}\left(q, F\right) \land \left(\left(\neg \left(\forall a \in Bool,\; \operatorname{EffectiveDescent}\left(q, Fa\left(a\right)\right)\right)\right) \land \left(\exists a \in Bool, x \in \operatorname{Fin}\left(3\right), y \in \operatorname{Fin}\left(3\right),\; q\left(x\right) = q\left(y\right) \land q\left(Fa\left(a, x\right)\right) \ne q\left(Fa\left(a, y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/PredictiveClosureInterventionSeparation.predictive_closure_not_intervention_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness uses one interface and a family of two updates. The false action is exactly the natural update, and that update descends through the interface.

The true action separates two states in the same interface fiber. Hence the shared action family is not closed under the interface even though its distinguished natural update is closed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/PredictiveClosureInterventionSeparation.predictive_closure_not_intervention_closure`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](../Dialectics/DeterministicInterfaceEquivalence.md)
