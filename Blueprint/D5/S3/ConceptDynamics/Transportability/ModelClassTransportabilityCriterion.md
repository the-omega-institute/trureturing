# Model-Class Transportability Criterion

## Abstract

Model-class transportability is exactly absence of a target residual.

**Theorem 1.1 (Transportability is equivalent to residual emptiness and kernel inclusion).**

$$\forall Model, Evidence, Target: Type,\\{}E: Model \to Evidence, T: Model \to Target,\\{}((\exists! \phi: \operatorname{range}\left(E\right) \to \operatorname{range}\left(T\right), \forall M: Model, \phi(\operatorname{rangeFactorization}\left(E, M\right)) = \operatorname{rangeFactorization}\left(T, M\right)) \Leftrightarrow \operatorname{TransRes}\left(E, T\right) = \emptyset) \land\\{}(\operatorname{TransRes}\left(E, T\right) = \emptyset \Leftrightarrow \operatorname{ker}\left(E\right) \subseteq \operatorname{ker}\left(T\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transportability/ModelClassTransportabilityCriterion.model_class_transportability_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evidence map records all available source experiments together with the target observational law. The target map records the target effect on the same model class.

TransRes is rendered by the repository's canonical defectRelation: its elements are precisely model pairs with equal evidence and unequal target values. No parallel residual definition is introduced.

Restricting both outputs to their realized images makes the computing map canonical and unique, including for an empty model class. The imported effective-image criterion supplies uniqueness and the kernel clause.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transportability/ModelClassTransportabilityCriterion.model_class_transportability_criterion`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion](../../ObserverMemory/Refinement/InterfaceKernelCriterion.md)
