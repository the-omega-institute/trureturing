# Indexed Target Sufficiency

## Abstract

An indexed local readout is target-sufficient exactly when its complete readout has no target-sensitive defect.

**Theorem 1.1 (Target stability, recovery, and empty defect are equivalent).**

$$\begin{aligned}\forall I, X, T: \operatorname{Type}, O: I \to \operatorname{Type},\\\operatorname{Nonempty}\left(X\right), q: \forall i: I, X \to O(i), t: X \to T \Rightarrow\\q_{all} = \operatorname{jointReadout}\left(q\right),\\(\operatorname{defectRelation}\left(q_{all}, t\right) = \emptyset \Leftrightarrow \forall x, y: X, (\forall i: I, \operatorname{q}\left(i, x\right) = \operatorname{q}\left(i, y\right)) \Rightarrow t(x) = t(y)) \land\\((\forall x, y: X, (\forall i: I, \operatorname{q}\left(i, x\right) = \operatorname{q}\left(i, y\right)) \Rightarrow t(x) = t(y)) \Leftrightarrow \exists r: \prod_{i: I}O(i) \to T, t = r \circ q_{all}) \land\\(\operatorname{defectRelation}\left(q_{all}, t\right) = \emptyset \Leftrightarrow \exists r: \prod_{i: I}O(i) \to T, t = r \circ q_{all}) \land\\\exists q0: \forall i: Unit, Bool \to Unit, t0: Bool \to Unit,\\{}\operatorname{defectRelation}\left(\operatorname{jointReadout}\left(q0\right), t0\right) = \emptyset \land \exists r: (Unit \to Unit) \to Unit, t0 = r \circ \operatorname{jointReadout}\left(q0\right) \land \neg \operatorname{Injective}\left(\operatorname{jointReadout}\left(q0\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.indexed_target_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete readout is constructed from the indexed local channels by collecting every coordinate into one dependent tuple. Its target defect contains exactly the state pairs that all channels merge while the target separates them.

On an inhabited state space, the accepted recovery criterion supplies a factor on the full dependent output type. Function extensionality identifies equality of complete readouts with coordinatewise local equivalence.

The final public witness uses the same constant local readout and constant target for its empty defect, recovery factor, and failure of state injectivity. It therefore shows that task sufficiency does not require recovering complete identity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency.indexed_target_sufficiency`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion](TargetRecoveryCriterion.md)
