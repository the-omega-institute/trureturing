# Chronological Signature Group-Like Hopf Laws

## Abstract

Finite step-two chronological signatures satisfy the group-like diagonal and antipode laws, and reverse-and-negate realizes the antipode on event words.

**Definition 1.1 (Group-like diagonal).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.groupLikeCoproduct`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.groupLikeCoproduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite group-like coproduct sends a signature to two identical copies.

**Theorem 1.2 (Multiplicative diagonal).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_mul`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal preserves chronological multiplication componentwise.

**Theorem 1.3 (Coassociative group-like diagonal).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_coassociative`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_coassociative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Either order of iterating the diagonal produces three identical signature components.

**Theorem 1.4 (Left antipode cancellation).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_left_convolution`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_left_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the antipode leg by the identity leg yields the empty signature.

**Theorem 1.5 (Right antipode cancellation).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_right_convolution`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_right_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the identity leg by the antipode leg yields the empty signature.

**Theorem 1.6 (Reverse-and-negate realizes the antipode).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing an event word and negating every observed value gives exactly the antipode of its chronological signature.

**Theorem 1.7 (Reverse-and-negate in logarithmic coordinates).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_log_reverse_neg`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_log_reverse_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After applying the logarithm, reverse-and-negate becomes coordinatewise negation.

**Theorem 1.8 (Involutive chronology reversal).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_involutive`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the finite antipode after reverse-and-negate recovers the original signature.

**Theorem 1.9 (Reversal of concatenation).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_append`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse-and-negate sends concatenation to the reversed product of the two antipodes.

## References

- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.groupLikeCoproduct`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_mul`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_coassociative`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_left_convolution`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_right_convolution`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_log_reverse_neg`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_involutive`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_append`
- Dependency: [D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm](StepTwoChronologicalLogarithm.md)
