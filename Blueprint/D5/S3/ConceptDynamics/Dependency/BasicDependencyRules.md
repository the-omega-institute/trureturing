# Basic Dependency Rules

## Abstract

Factorization dependence is closed under identity, composition, and joint readouts.

**Theorem 1.1 (Concept dependence obeys the basic rules).**

$$\begin{gathered}\forall X, A, B, C, D: \operatorname{Type},\\{}q_{A}: X \to A, q_{B}: X \to B,\\{}q_{C}: X \to C, q_{D}: X \to D,\\{}\operatorname{Refines}\left(q_{A}, q_{A}\right) \land\\{}(\operatorname{Refines}\left(q_{A}, \operatorname{conceptJoin}\left(q_{A}, q_{B}\right)\right) \land \operatorname{Refines}\left(q_{B}, \operatorname{conceptJoin}\left(q_{A}, q_{B}\right)\right)) \land\\{}(\operatorname{Refines}\left(q_{B}, q_{A}\right) \land \operatorname{Refines}\left(q_{C}, q_{B}\right)) \Rightarrow \operatorname{Refines}\left(q_{C}, q_{A}\right) \land\\{}(\operatorname{Refines}\left(q_{B}, q_{A}\right) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(q_{B}, q_{C}\right), \operatorname{conceptJoin}\left(q_{A}, q_{C}\right)\right)) \land\\{}(\operatorname{Refines}\left(q_{B}, q_{A}\right) \land \operatorname{Refines}\left(q_{C}, q_{A}\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(q_{B}, q_{C}\right), q_{A}\right) \land\\{}\operatorname{Refines}\left(\operatorname{conceptJoin}\left(q_{B}, q_{C}\right), q_{A}\right) \Rightarrow (\operatorname{Refines}\left(q_{B}, q_{A}\right) \land \operatorname{Refines}\left(q_{C}, q_{A}\right)) \land\\{}(\operatorname{Refines}\left(q_{B}, q_{A}\right) \land \operatorname{Refines}\left(q_{D}, \operatorname{conceptJoin}\left(q_{B}, q_{C}\right)\right)) \Rightarrow \operatorname{Refines}\left(q_{D}, \operatorname{conceptJoin}\left(q_{A}, q_{C}\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dependency/BasicDependencyRules.basic_dependency_rules` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity and composition of factor maps give reflexivity and transitivity. Product projections, paired factor maps, and preservation of a shared coordinate give projection, augmentation, merge, decomposition, and pseudotransitivity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dependency/BasicDependencyRules.basic_dependency_rules`
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
