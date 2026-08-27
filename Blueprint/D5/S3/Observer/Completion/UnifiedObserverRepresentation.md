# Unified Observer Representation

## Abstract

The complete protocol signature has a canonical quotient-range representation and three equivalent factorization tests.

**Theorem 1.1 (Canonical signature quotient and universal observer factorization).**

$$\begin{gathered}\forall X, P, L, R: \operatorname{Type},\\{}law: P \to \left(X \to L\right), r: X \to R,\\{}\exists! E: \operatorname{quotient}(\operatorname{ker}(\operatorname{completeSignature}(law))) \to \operatorname{range}(\operatorname{completeSignature}(law)), \forall x: X, E(\operatorname{quotientClass}(\operatorname{ker}(\operatorname{completeSignature}(law)), x)) = \operatorname{realizedPair}(\operatorname{completeSignature}(law)(x), \operatorname{witness}(x)) \land\\{}(\forall protocol: P, \exists kProtocol: \operatorname{range}(r) \to L, law(protocol) = kProtocol \circ \operatorname{rangeFactorization}(r) \iff \forall x: X, y: X, r(x) = r(y) \Rightarrow \operatorname{completeSignature}(law)(x) = \operatorname{completeSignature}(law)(y)) \land\\{}(\forall x: X, y: X, r(x) = r(y) \Rightarrow \operatorname{completeSignature}(law)(x) = \operatorname{completeSignature}(law)(y) \iff \exists! phi: \operatorname{range}(r) \to \operatorname{range}(\operatorname{completeSignature}(law)), \operatorname{rangeFactorization}(\operatorname{completeSignature}(law)) = phi \circ \operatorname{rangeFactorization}(r)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/UnifiedObserverRepresentation.unified_observer_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete signature sends a source state to the protocol-indexed family of laws. Its equality-kernel quotient is canonically equivalent to the realized signature range, with the equivalence fixed on every state.

For an interface r, factorization of every protocol law through the realized interface image is equivalent to inclusion of the interface kernel in the complete-signature kernel. The same condition is equivalent to the unique map from the realized interface image into the signature image.

## References

- Truth anchor: `D5/S3/Observer/Completion/UnifiedObserverRepresentation.unified_observer_representation`
