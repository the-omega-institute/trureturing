# Recursive Signature Completion

## Abstract

Recursive signatures recover finite-future classes and their stable completion.

**Theorem 1.1 (Signature labels equal finite future classes).**

$$\begin{gathered}\forall Y, O, [\operatorname{Fintype}(Y)], [\operatorname{Fintype}(O)],\\{}\tau: Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\{}(\forall m \geq 0, y, y'\in Y, c_{m}(y) = c_{m}(y') \iff y \equiv_{m}^{q} y') \land\\{}\min\{m \mid c_{m+1} \sim c_{m}\} = m_{*} \land\\{}E: c_{m_{*}}(Y) \equiv Y/\equiv_{\infty}^{q}, \forall y\in Y, E(c_{m_{*}}(y)) = [y]_{\equiv_{\infty}^{q}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Prediction/RecursiveSignatureCompletion.recursive_signature_labels_stable_depth_and_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y and O be finite, let the deterministic update be tau, and let q map Y surjectively onto the actual readout carrier O. The depth-zero label is q itself. Each later label is the pair consisting of the current readout and the preceding label after one update.

Induction identifies equality of these recursively constructed labels with equality of every readout through the same finite horizon. Consequently the first adjacent pair of label partitions that agree occurs at exactly the canonical finite-observation stability depth.

At that depth, the first-isomorphism equivalence sends realized labels to the finite prediction quotient. The existing stable quotient equivalence then gives the named canonical map to complete-future state classes, and its representative equation sends the label of y to the complete quotient class of y.

## References

- Truth anchor: `D5/S3/Observer/Prediction/RecursiveSignatureCompletion.recursive_signature_labels_stable_depth_and_completion`
- Dependency: [D5/S3/Observer/Separation/FiniteObservationRefinementBound](../Separation/FiniteObservationRefinementBound.md)
