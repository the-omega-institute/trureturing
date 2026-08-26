# Target Sufficiency

## Abstract

Target residual emptiness is exactly target stability on local observation fibers.

**Lemma 1.1 (Empty target residuals are target-closure fixed points).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type}, q: X \to B, t: X \to Y,\\{}[\operatorname{Nonempty}\left(X\right)], \operatorname{targetResidual}\left(q, t\right) = \emptyset \iff \operatorname{ConceptEquivalent}\left(\operatorname{targetClosure}\left(q, t\right), q\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetSufficiency.target_residual_empty_iff_target_closure_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an inhabited state type, the newly named target residual is the existing defect relation. Its emptiness is therefore the existing fiber-constancy condition.

The imported target-closure theorem identifies fixed points with canonical target refinement, while the existing universal factorization theorem identifies that refinement with the same fiber condition.

**Theorem 1.2 (The three target-sufficiency conditions are equivalent).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type}, q: X \to B, t: X \to Y,\\{}[\operatorname{Nonempty}\left(Y\right)], (\operatorname{targetResidual}\left(q, t\right) = \emptyset \iff \forall x, y: X, q(x) = q(y) \Rightarrow t(x) = t(y)) \land\\{}(\forall x, y: X, q(x) = q(y) \Rightarrow t(x) = t(y) \iff \exists barT: B \to Y, t = barT \circ q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetSufficiency.target_sufficiency_three_way` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target residual is empty exactly when every pair with the same single-readout coordinate has the same target value. Thus local indistinguishability means literal equality under q.

Mathlib's factors-through criterion turns fiber constancy into a total decoder on the raw codomain of q. Nonempty Y supplies a value on coordinates outside the realized range of q.

This single-readout statement uses q in place of the source's q_all. A quotient lift would avoid choice only after replacing q by its kernel quotient projection, which is a different factorization.

**Lemma 1.3 (Inhabited states are needed by the closure bridge).**

$$qEmpty: Empty \to Unit, tEmpty: Empty \to Empty, \operatorname{targetResidual}\left(qEmpty, tEmpty\right) = \emptyset \land \neg \operatorname{ConceptEquivalent}\left(\operatorname{targetClosure}\left(qEmpty, tEmpty\right), qEmpty\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetSufficiency.nonempty_state_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take Empty states, Unit observations, and an Empty-valued target. The target residual is empty because there are no state pairs.

Target closure nevertheless has an empty target-image coordinate. A reverse refinement from Unit would construct an element of that empty image, so closure equivalence fails.

**Lemma 1.4 (An empty target type blocks a total decoder).**

$$qEmpty: Empty \to Unit, tEmpty: Empty \to Empty,\\{}\operatorname{targetResidual}\left(qEmpty, tEmpty\right) = \emptyset \land \forall x, y: Empty, qEmpty(x) = qEmpty(y) \Rightarrow tEmpty(x) = tEmpty(y) \land\\{}\neg \exists barT: Unit \to Empty, tEmpty = barT \circ qEmpty.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/TargetSufficiency.nonempty_target_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Again use Empty states, Unit observations, and an Empty target type. Residual emptiness and fiber constancy both hold vacuously.

A total factor through the raw observation codomain would include a function from Unit to Empty. Evaluating it at the unit value is impossible, so target inhabitedness cannot simply be deleted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetSufficiency.nonempty_state_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetSufficiency.nonempty_target_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetSufficiency.target_residual_empty_iff_target_closure_fixed`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/TargetSufficiency.target_sufficiency_three_way`
- Dependency: [D5/S3/ConceptDynamics/Completion/TargetClosureOperator](TargetClosureOperator.md)
- Dependency: [D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion](../Restoration/TargetRecoveryCriterion.md)
