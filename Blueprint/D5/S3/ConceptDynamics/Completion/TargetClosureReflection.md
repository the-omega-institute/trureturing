# Target Closure Reflection

## Abstract

Target closure is the least target-sufficient refinement and reflects into the target-sufficient concepts.

**Lemma 1.1 (Target sufficiency is constancy on concept fibers).**

$$\begin{gathered}\forall X, D, Y: \operatorname{Type},\\{}\operatorname{Nonempty}\left(X\right), q_{D}: X \to D, T: X \to Y,\\{}\operatorname{TargetSufficient}\left(q_{D}, T\right) \iff \forall x, y: X, q_{D}(x) = q_{D}(y) \Rightarrow T(x) = T(y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_sufficient_iff_fiber_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty state space, a concept is target-sufficient exactly when the target takes the same value on every pair of states that the concept readout identifies.

Equivalently, the canonical target-image readout factors through the concept precisely when the target is constant on each concept fiber.

**Theorem 1.2 (Target closure has the reflection universal property).**

$$\begin{gathered}\forall X, B, D, Y: \operatorname{Type},\\{}q_{C}: X \to B, q_{D}: X \to D, T: X \to Y,\\{}\operatorname{TargetSufficient}\left(q_{D}, T\right) \Rightarrow (\operatorname{Refines}\left(\operatorname{targetClosure}\left(q_{C}, T\right), q_{D}\right) \iff \operatorname{Refines}\left(q_{C}, q_{D}\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_closure_reflection_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a target-sufficient comparison concept. The target closure of a concept refines that comparison exactly when the original concept already refines it.

One direction follows because the original concept refines its closure. For the other, the comparison receives both the original concept and the canonical target readout, so the universal property of their join supplies the required factorization.

**Lemma 1.3 (Target closure is the least target-sufficient refinement).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}q_{C}: X \to B, T: X \to Y,\\{}\operatorname{TargetSufficient}\left(\operatorname{targetClosure}\left(q_{C}, T\right), T\right) \land\\{}\operatorname{Refines}\left(q_{C}, \operatorname{targetClosure}\left(q_{C}, T\right)\right) \land\\{}\forall D: \operatorname{Type}, q_{D}: X \to D,\\{}(\operatorname{TargetSufficient}\left(q_{D}, T\right) \land \operatorname{Refines}\left(q_{C}, q_{D}\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{targetClosure}\left(q_{C}, T\right), q_{D}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_closure_is_least_target_sufficient_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Target closure is itself target-sufficient and refines the original concept by adjoining only the canonical target coordinate.

Every target-sufficient concept that refines the original concept also receives a factor map from the closure. These three properties make the closure the least target-sufficient refinement in the concept refinement order.

**Lemma 1.4 (Target closure is a target-sufficient fixed point).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}q_{C}: X \to B, T: X \to Y,\\{}\operatorname{TargetSufficient}\left(\operatorname{targetClosure}\left(q_{C}, T\right), T\right) \land\\{}\operatorname{ConceptEquivalent}\left(\operatorname{targetClosure}\left(\operatorname{targetClosure}\left(q_{C}, T\right), T\right), \operatorname{targetClosure}\left(q_{C}, T\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_closure_is_target_sufficient_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Completing a concept makes the target recoverable from its readout. Completing the result again adds no new distinctions: the twice-completed readout and the once-completed readout mutually refine one another.

Thus target closure lands among the target-sufficient concepts and is idempotent there up to concept equivalence.

**Lemma 1.5 (Target sufficiency is necessary for the reflection equivalence).**

$$\begin{gathered}\exists q_{C}, q_{D}: \operatorname{Concept}\left(Bool, Unit\right),\\{}\neg \operatorname{TargetSufficient}\left(q_{D}, id_{Bool}\right) \land\\{}\operatorname{Refines}\left(q_{C}, q_{D}\right) \land\\{}\neg \operatorname{Refines}\left(\operatorname{targetClosure}\left(q_{C}, id_{Bool}\right), q_{D}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_sufficiency_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take both concepts to be the constant readout from the two Boolean states to the one-point type, and take the target to be the Boolean identity. The two concepts refine one another, but neither can recover the target.

The target closure records the Boolean target coordinate and therefore distinguishes false from true. It cannot factor through the one-point comparison concept, which witnesses failure of the reflection equivalence when target sufficiency is omitted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_closure_is_least_target_sufficient_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_closure_is_target_sufficient_fixed_point`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_closure_reflection_universal`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_sufficiency_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetClosureReflection.target_sufficient_iff_fiber_constant`
- Dependency: [D5/S3/ConceptDynamics/Completion/TargetClosureOperator](TargetClosureOperator.md)
