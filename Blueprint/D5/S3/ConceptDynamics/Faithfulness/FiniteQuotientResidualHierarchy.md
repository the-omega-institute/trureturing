# Finite Quotient Languages and Their Residual Hierarchy

## Abstract

Finite nilpotent quotient observations lie inside the finite solvable quotient observations, which lie inside all finite quotient observations; their kernel residuals are ordered in reverse.

**Theorem 1.1 (Larger quotient languages have smaller common kernels).**

$$\forall G, \operatorname{Group}\left(G\right) \Rightarrow\\{}(\operatorname{nilpotentQuotientLanguage}\left(G\right) \subseteq \operatorname{solvableQuotientLanguage}\left(G\right)) \land\\{}(\operatorname{solvableQuotientLanguage}\left(G\right) \subseteq \operatorname{finiteQuotientLanguage}\left(G\right)) \land\\{}(\operatorname{finiteResidual}\left(G\right) \subseteq \operatorname{solvableResidual}\left(G\right)) \land\\{}(\operatorname{solvableResidual}\left(G\right) \subseteq \operatorname{nilpotentResidual}\left(G\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientResidualHierarchy.finite_quotient_residual_hierarchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quotient channel is represented canonically by a normal subgroup and its quotient map. The finite, finite solvable, and finite nilpotent languages select channels by properties of those quotient targets.

Every nilpotent group is solvable, while finiteness is explicitly retained when a nilpotent channel is viewed as solvable and when a solvable channel is viewed as finite. These facts give the first two displayed language inclusions on the same normal-quotient carrier.

The finite residual is the frozen object from the adjacent finite-quotient faithfulness theorem. The other residuals intersect the kernels over the selected solvable and nilpotent languages. An intersection over more channels is smaller, giving both displayed reverse inclusions. This closes atom generic-residual-1af9114aad5514c525c71e338c1ccb4f142b4afe6fedc0d198daa73a4e456caa.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientResidualHierarchy.finite_quotient_residual_hierarchy`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel](FiniteQuotientJointKernel.md)
