# Canonical Signature Completion

## Abstract

Canonical signatures recover finite words, the canonical stable depth, and completion.

**Theorem 1.1 (Canonical signatures equal finite future classes).**

$$\begin{gathered}\forall Y, O, [\operatorname{Fintype}(Y)], [\operatorname{Fintype}(O)], [\operatorname{Nonempty}(Y)],\\{}\tau: Y \to Y, q: Y \to O,\\{}\operatorname{Surjective}(q),\\{}(\forall m, y, y', controlledSignature_{m}(y) = controlledSignature_{m}(y') \iff y \equiv_{m}^{q} y') \land\\{}ker(controlledSignature_{m_{*}}) = ker(controlledSignature_{m_{*}+1}) \land\\{}(\forall m, ker(controlledSignature_{m}) = ker(controlledSignature_{m+1}) \Rightarrow m_{*} \leq m) \land\\{}E: \operatorname{range}(controlledSignature_{m_{*}}) \equiv Z_{q}, \forall y\in Y, E(controlledSignature_{m_{*}}(y)) = [y]_{Z_{q}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Prediction/CanonicalSignatureCompletion.canonical_signature_labels_stable_depth_and_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y and O be finite, let tau be a deterministic update, and let q be a surjective readout. The canonical controlled-signature algorithm is specialized to the singleton input carrier, so its input words are exactly finite iterates of tau.

The imported controlled-signature correctness theorem then identifies signature equality with the finite-future relation at every depth. The imported observation refinement theorem supplies the existing least adjacent-partition stability depth directly.

At that canonical depth, the first-isomorphism equivalence for the controlled-signature map is followed by the existing stable finite-to-complete quotient equivalence. The resulting named map sends every realized signature to the complete class of its state.

## References

- Truth anchor: `D5/S3/Observer/Prediction/CanonicalSignatureCompletion.canonical_signature_labels_stable_depth_and_completion`
- Dependency: [D5/S3/Observer/Separation/FiniteObservationRefinementBound](../Separation/FiniteObservationRefinementBound.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization](../../ObserverMemory/Algorithms/ControlledSignatureStabilization.md)
