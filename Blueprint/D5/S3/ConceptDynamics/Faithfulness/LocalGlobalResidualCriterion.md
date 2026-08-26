# Local-Global Residual Criterion

## Abstract

The dependent residual of distinct states invisible to every local readout is empty exactly when the joint readout is injective.

**Theorem 1.1 (Residual emptiness is joint injectivity).**

$$\begin{aligned}\forall I, X: \operatorname{Type}, V: I \to \operatorname{Type},\\q: \forall i: I, X \to \operatorname{V}\left(i\right),\\\operatorname{IsEmpty}\left(\{(x, y): X \times X \mid x \neq y \land \forall i: I, \operatorname{q}\left(i, x\right) = \operatorname{q}\left(i, y\right)\}\right) \iff \operatorname{Injective}\left(\operatorname{jointReadout}\left(q\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion.local_global_residual_empty_iff_joint_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an indexed dependent family q_i : X -> V_i, the residual is the dependent type of pairs of distinct states whose readings agree at every index.

Emptiness of this residual says that coordinatewise equality separates states. The canonical jointReadout packages exactly those coordinate values, so the frozen joint-faithfulness criterion identifies this separation property with injectivity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/LocalGlobalResidualCriterion.local_global_residual_empty_iff_joint_injective`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](JointFaithfulnessLeibnizCriterion.md)
