# Truncated Tensor Signature

## Abstract

Universal degree-two tensor signatures obey Chen concatenation.

**Definition 1.1 (Tensor-square signature).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universal step-two coordinate stores degree one in a module and twice degree two in its genuine tensor square.

**Definition 1.2 (Single-event tensor signature).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.eventTensorSignature`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.eventTensorSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One event contributes its vector and its pure tensor square.

**Definition 1.3 (Chronological tensor word signature).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronologicalTensorSignature`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronologicalTensorSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A list is folded from left to right using chronological tensor composition.

**Theorem 1.4 (Tensor Chen concatenation).**

$$\forall f, P, S, \operatorname{chronologicalTensorSignature}(f, \operatorname{append}(P, S)) = \operatorname{chronologicalTensorSignature}(f, P) \cdot \operatorname{chronologicalTensorSignature}(f, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signature of an earlier word followed by a later word is their chronological product.

**Theorem 1.5 (Degree-one word sum).**

$$\forall f, L, \operatorname{degreeOne}(\operatorname{chronologicalTensorSignature}(f, L)) = \operatorname{sum}(\operatorname{map}(f, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_degree_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree-one coordinate is the ordinary sum of all event vectors.

**Theorem 1.6 (Explicit two-event signature).**

$$\begin{gathered}\operatorname{degreeOne}(\operatorname{chronologicalTensorSignature}(f, [x, y])) = x + y\\\operatorname{doubledDegreeTwo}(\operatorname{chronologicalTensorSignature}(f, [x, y])) = \operatorname{tensor}(x, x) + 2 \cdot \operatorname{tensor}(x, y) + \operatorname{tensor}(y, y)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_two_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two events exhibit the pure squares and twice the ordered tensor cross term.

## References

- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronologicalTensorSignature`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_append`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_degree_one`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_two_events`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.eventTensorSignature`
