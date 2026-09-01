# Truncated Tensor Group-Like Laws

## Abstract

Tensor flip characterizes the group-like degree-two equation and preserves chronological Chen products.

**Definition 1.1 (Tensor-square flip).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorHopf.tensorFlip`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorHopf.tensorFlip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical linear involution exchanges the two tensor factors.

**Definition 1.2 (Doubled group-like equation).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorHopf.IsStepTwoGroupLike`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorHopf.IsStepTwoGroupLike` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A signature is group-like through degree two when its symmetric tensor part equals twice the pure square of degree one.

**Theorem 1.3 (Tensor flip is involutive).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorHopf.tensor_flip_involutive`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorHopf.tensor_flip_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the canonical flip twice recovers every tensor.

**Theorem 1.4 (Single events are group-like).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorHopf.event_tensor_signature_isStepTwoGroupLike`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorHopf.event_tensor_signature_isStepTwoGroupLike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pure square carried by one event satisfies the doubled group-like equation.

**Theorem 1.5 (Chen multiplication preserves group-like signatures).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorHopf.isStepTwoGroupLike_mul`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorHopf.isStepTwoGroupLike_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The group-like equation is closed under the ordered degree-two Chen product.

**Theorem 1.6 (Chronological words are group-like).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorHopf.chronological_tensor_signature_isStepTwoGroupLike`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorHopf.chronological_tensor_signature_isStepTwoGroupLike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite event word inherits the group-like equation from its single-event factors.

**Theorem 1.7 (Word symmetric part is fixed by degree one).**

Lean statement: `D5/S3/Observer/Chronology/TruncatedTensorHopf.chronological_tensor_signature_symmetric_part`

*Formalization.* `D5/S3/Observer/Chronology/TruncatedTensorHopf.chronological_tensor_signature_symmetric_part` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word, tensor degree one determines the complete symmetric part of doubled degree two.

## References

- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorHopf.tensorFlip`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorHopf.IsStepTwoGroupLike`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorHopf.tensor_flip_involutive`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorHopf.event_tensor_signature_isStepTwoGroupLike`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorHopf.isStepTwoGroupLike_mul`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorHopf.chronological_tensor_signature_isStepTwoGroupLike`
- Truth anchor: `D5/S3/Observer/Chronology/TruncatedTensorHopf.chronological_tensor_signature_symmetric_part`
- Dependency: [D5/S3/Observer/Chronology/TruncatedTensorSignature](TruncatedTensorSignature.md)
