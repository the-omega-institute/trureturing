# Joint Faithfulness and the Leibniz Criterion

## Abstract

Joint faithfulness is exactly state separation by an indexed concept family, and constant readouts show that the condition is substantive.

**Theorem 1.1 (Joint faithfulness, point separation, and diagonal kernels coincide).**

$$\begin{aligned}\forall I, X: \operatorname{Type}, V: I \to \operatorname{Type},\\q: \forall i: I, X \to \operatorname{V}\left(i\right),\\\operatorname{Injective}\left(\operatorname{jointReadout}\left(q\right)\right) \iff (\forall x, y: X, (\forall i: I, \operatorname{q}\left(i, x\right) = \operatorname{q}\left(i, y\right)) \Rightarrow x = y) \iff \operatorname{jointKernel}\left(q\right) = \operatorname{diagonal}\left(X\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.joint_faithfulness_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an indexed family of readouts q_i : X -> V_i, the joint readout records every component value at once. It is injective exactly when equality of all component readings forces equality of the underlying states.

The kernel of the family is the intersection of the component kernels. A pair lies in this intersection precisely when every readout assigns the pair equal values, so point separation says that this intersection contains no pairs beyond the equality diagonal.

Equality of two dependent joint outputs is componentwise equality. This identifies joint-readout injectivity with point separation; the same componentwise condition identifies point separation with equality between the joint kernel and the diagonal.

**Theorem 1.2 (A constant concept family is not jointly faithful).**

$$\begin{aligned}\exists q: (\forall i: Unit, Bool \to Unit),\\(\exists x, y: Bool, x \neq y \land \forall i, \operatorname{q}\left(i, x\right) = \operatorname{q}\left(i, y\right))\\\land \neg \operatorname{Injective}\left(\operatorname{jointReadout}\left(q\right)\right)\\\land \neg (\forall x, y: Bool, (\forall i: Unit, \operatorname{q}\left(i, x\right) = \operatorname{q}\left(i, y\right)) \Rightarrow x = y)\\\land \operatorname{jointKernel}\left(q\right) \ne \operatorname{diagonal}\left(Bool\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.constant_concept_family_not_jointly_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the family indexed by the singleton type whose only readout maps both Boolean states to the unique element of Unit. The distinct states false and true therefore have equal readings in every component and equal joint outputs.

Consequently the joint readout is not injective and the point-separation condition fails. The pair (false, true) also belongs to every component kernel while lying off the Boolean diagonal, so the joint kernel is not the diagonal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.constant_concept_family_not_jointly_faithful`
- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.joint_faithfulness_tfae`
