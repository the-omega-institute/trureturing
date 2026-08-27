# Behavior Update Word Action

## Abstract

Controlled behavior updates descend to the realized range and compose along words.

**Theorem 1.1 (Behavior updates are representative-independent and act by words).**

$$\begin{gathered}\forall U, Y, O: Type,\\{}\forall F: U \to \left(Y \to Y\right), q: Y \to O,\\{}(\forall u: U, y, y_{p}: Y, \operatorname{controlledBehavior}(F, q, y) = \operatorname{controlledBehavior}(F, q, y_{p}) \Rightarrow \operatorname{controlledBehavior}(F, q, F(u)(y)) = \operatorname{controlledBehavior}(F, q, F(u)(y_{p}))) \land\\{}(\forall u: U, y: Y, \operatorname{behaviorUpdate}(F, q, u)(\operatorname{rangeFactorization}(\operatorname{controlledBehavior}(F, q), y)) = \operatorname{rangeFactorization}(\operatorname{controlledBehavior}(F, q), F(u)(y))) \land\\{}(\forall b: \operatorname{range}(\operatorname{controlledBehavior}(F, q)), \operatorname{behaviorWordUpdate}(F, q, \operatorname{nil}(U))(b) = b) \land\\{}(\forall v, w: \operatorname{List}(U), b: \operatorname{range}(\operatorname{controlledBehavior}(F, q)), \operatorname{behaviorWordUpdate}(F, q, \operatorname{append}(v, w))(b) = \operatorname{behaviorWordUpdate}(F, q, w)(\operatorname{behaviorWordUpdate}(F, q, v)(b))) \land\\{}(\forall w: \operatorname{List}(U), y: Y, \operatorname{behaviorWordUpdate}(F, q, w)(\operatorname{rangeFactorization}(\operatorname{controlledBehavior}(F, q), y)) = \operatorname{rangeFactorization}(\operatorname{controlledBehavior}(F, q), \operatorname{runWord}(F, w, y))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/BehaviorUpdateWordAction.behavior_update_well_defined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of complete controlled behaviors is preserved after every input. The one-input update is transported through the canonical quotient-to-range equivalence, so it lives on the exact realized behavior range.

The named word update has the empty-word and concatenation laws. Its value on every realized behavior is the behavior of the source state after the imported left-to-right word execution.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorUpdateWordAction.behavior_update_well_defined`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../Prediction/ControlledBehaviorUniversality.md)
