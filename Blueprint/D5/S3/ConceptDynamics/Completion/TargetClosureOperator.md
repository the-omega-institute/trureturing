# Target Closure Operator

## Abstract

Joining a concept with the canonical target readout defines a closure operation.

**Theorem 1.1 (Target completion obeys the three closure laws).**

$$\begin{gathered}\forall X, B, D, Y: \operatorname{Type},\\{}q_{C}: X \to B, q_{D}: X \to D, T: X \to Y,\\{}\operatorname{Refines}\left(q_{C}, \operatorname{targetClosure}\left(q_{C}, T\right)\right) \land\\{}(\operatorname{Refines}\left(q_{C}, q_{D}\right) \Rightarrow \operatorname{Refines}\left(\operatorname{targetClosure}\left(q_{C}, T\right), \operatorname{targetClosure}\left(q_{D}, T\right)\right)) \land\\{}\operatorname{ConceptEquivalent}\left(\operatorname{targetClosure}\left(\operatorname{targetClosure}\left(q_{C}, T\right), T\right), \operatorname{targetClosure}\left(q_{C}, T\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetClosureOperator.target_closure_three_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Target completion adjoins the canonical target-image readout to a concept readout. Projection onto the original coordinate shows that completion is extensive in the refinement order.

A factor map between two concept readouts lifts to their completions by applying it to the concept coordinate and preserving the shared target coordinate, which proves monotonicity.

Completing twice adds a second copy of the same target coordinate. Duplicating that coordinate and forgetting the duplicate give mutual refinements, so idempotence holds up to concept equivalence despite the changed product codomain.

**Lemma 1.2 (Fixed points are exactly target-sufficient concepts).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}q_{C}: X \to B, T: X \to Y,\\{}\operatorname{ConceptEquivalent}\left(\operatorname{targetClosure}\left(q_{C}, T\right), q_{C}\right) \iff \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), q_{C}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetClosureOperator.target_closure_equivalent_iff_target_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept is unchanged by target completion, up to mutual refinement, exactly when its readout already determines the canonical target readout. In that case adjoining the target adds no distinctions.

Conversely, if completion is equivalent to the original concept, the target projection through the completed readout composes with that equivalence to factor the target through the original concept.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetClosureOperator.target_closure_equivalent_iff_target_sufficient`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetClosureOperator.target_closure_three_laws`
- Dependency: [D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak](../Disclosure/ExactTargetForcedLeak.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
