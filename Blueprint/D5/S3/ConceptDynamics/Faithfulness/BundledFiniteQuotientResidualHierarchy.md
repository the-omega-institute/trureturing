# Bundled Finite Quotient Residual Hierarchy

## Abstract

Finite nilpotent quotient observations form a sublanguage of the finite solvable quotient observations, and their residual intersections are ordered in reverse.

**Theorem 1.1 (Restricting bundled quotient languages enlarges residuals).**

$$\forall G, \operatorname{Group}\left(G\right) \Rightarrow\\{}(\operatorname{nilpotentFiniteQuotientLanguage}\left(G\right) \subseteq \operatorname{solvableFiniteQuotientLanguage}\left(G\right)) \land\\{}(\operatorname{finiteResidual}\left(G\right) \subseteq \operatorname{solvableFiniteResidual}\left(G\right)) \land\\{}(\operatorname{solvableFiniteResidual}\left(G\right) \subseteq \operatorname{nilpotentFiniteResidual}\left(G\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/BundledFiniteQuotientResidualHierarchy.bundled_finite_quotient_residual_hierarchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation carrier is Mathlib's bundled finite-index normal subgroup type. Solvable and nilpotent languages are predicates on that carrier, so finiteness is already part of every channel.

A nilpotent quotient is solvable. The finite residual is the canonical intersection supplied by the adjacent joint-kernel theorem; the other residuals intersect only the bundled channels satisfying their respective predicates.

Intersecting over all finite quotients is contained in the solvable intersection, and the solvable intersection is contained in the nilpotent intersection. This closes atom generic-residual-1af9114aad5514c525c71e338c1ccb4f142b4afe6fedc0d198daa73a4e456caa.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/BundledFiniteQuotientResidualHierarchy.bundled_finite_quotient_residual_hierarchy`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel](FiniteQuotientJointKernel.md)
