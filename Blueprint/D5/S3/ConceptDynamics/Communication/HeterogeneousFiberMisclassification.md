# Heterogeneous Fiber Misclassification

## Abstract

A message fiber with two target values forces a deterministic error.

**Theorem 1.1 (A heterogeneous message fiber forces an error).**

$$\begin{gathered}\forall X, M, Y: \operatorname{Type},\\{}M_{S}: X \to M, T: X \to Y,\\{}\forall x, y: X,\\{}(M_{S}(x) = M_{S}(y) \land T(x) \neq T(y)) \Rightarrow \\{}\forall delta: M \to Y, (delta(M_{S}(x)) \neq T(x) \lor delta(M_{S}(y)) \neq T(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/HeterogeneousFiberMisclassification.heterogeneous_fiber_forces_misclassification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The message and target are arbitrary readouts on one state carrier. Two named states witness heterogeneity by sharing a message while having different target values.

Every deterministic inference rule is represented by a function from messages to target values. The public conclusion says directly that its inferred value is wrong at the first witness or at the second witness.

Equal messages force equal inferred values. If both inferences were correct, equality transport would contradict the displayed target inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/HeterogeneousFiberMisclassification.heterogeneous_fiber_forces_misclassification`
