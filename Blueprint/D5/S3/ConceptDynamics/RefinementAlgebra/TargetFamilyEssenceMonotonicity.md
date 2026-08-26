# Target-Family Essence Monotonicity

## Abstract

The minimally sufficient joint target becomes finer under family enlargement.

**Theorem 1.1 (Joint target minimality and family monotonicity).**

$$\begin{aligned}\forall X: \operatorname{Type}, I: \operatorname{Type}, B: \operatorname{Type},\\Y: I \to \operatorname{Type}, T: \forall i: I, X \to Y(i),\\R: X \to B,\\{}[((\forall i: I, \operatorname{Refines}(T(i), R)) \iff \operatorname{Refines}(\operatorname{jointTarget}(T), R)) \land\\(\forall i: I, \operatorname{Refines}(T(i), \operatorname{jointTarget}(T))) \land \forall D: \operatorname{Type}, q: X \to D, (\forall i: I, \operatorname{Refines}(T(i), q)) \Rightarrow \operatorname{Refines}(\operatorname{jointTarget}(T), q)] \land\\(\forall J: \operatorname{Type}, Z: J \to \operatorname{Type}, A: \forall j: J, X \to Z(j), \operatorname{Refines}(\operatorname{jointTarget}(T), \operatorname{jointTarget}(\operatorname{sumTarget}(T, A)))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/TargetFamilyEssenceMonotonicity.multi_target_essence_sufficiency_and_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source's canonical essence for a target family is the existing jointTarget. A readout decides it exactly when the readout decides every component target.

The joint target decides each component and is coarsest among all simultaneously sufficient concepts. These clauses are supplied by the frozen dependent-family theorem.

The public enlargement clause uses the named sumTarget construction. It adjoins an arbitrary dependent family, and restriction along the left injection proves that the enlarged essence refines the old one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/TargetFamilyEssenceMonotonicity.multi_target_essence_sufficiency_and_monotonicity`
- Dependency: [D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency](../Refinement/MultiTargetMinimalSufficiency.md)
