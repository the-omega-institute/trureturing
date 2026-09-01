# Truncated Tensor Chronological Signature

## Abstract

Degree-two tensor signatures carry Chen multiplication and finite chronological word signatures.

**Definition 1.1 (Doubled tensor signature).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A normalized step-two signature stores degree one together with twice tensor degree two.

**Definition 1.2 (Step-two Chen multiplication).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature.compose`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature.compose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composition adds degree one and inserts twice the ordered cross tensor at degree two.

**Definition 1.3 (Single-event tensor signature).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.eventTensorSignature`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.eventTensorSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One event contributes its value in degree one and its pure square tensor in doubled degree two.

**Definition 1.4 (Chronological tensor word signature).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronologicalTensorSignature`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronologicalTensorSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite event list is folded in operational order using the Chen product.

**Theorem 1.5 (Tensor Chen append identity).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_append`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signature of an earlier word followed by a later word is the product of their tensor signatures.

**Theorem 1.6 (Degree one is the event sum).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_degree_one`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_degree_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first tensor degree forgets chronology and equals the ordinary sum of observed event values.

**Theorem 1.7 (Two-event ordered cross tensor).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_two_events`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_two_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree-two coordinate of two events contains the ordered cross tensor with coefficient two.

## References

- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.TensorSignature.compose`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.eventTensorSignature`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronologicalTensorSignature`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_append`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_degree_one`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorSignature.chronological_tensor_signature_two_events`
