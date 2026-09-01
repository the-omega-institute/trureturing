# Chronological Signature Group-Like Hopf Laws

## Abstract

Step-two chronological signatures satisfy the group-like coproduct and antipode laws, and the antipode reverses event order with negated values.

**Definition 1.1 (Group-like diagonal).**

Lean statement: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.groupLikeCoproduct`

*Formalization.* `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.groupLikeCoproduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite group-like coproduct sends a signature to two identical copies.

**Theorem 1.2 (Multiplicative diagonal).**

$$\forall a, b, \operatorname{groupLikeCoproduct}(a \cdot b) = (\operatorname{fst}(\operatorname{groupLikeCoproduct}(a)) \cdot \operatorname{fst}(\operatorname{groupLikeCoproduct}(b)), \operatorname{snd}(\operatorname{groupLikeCoproduct}(a)) \cdot \operatorname{snd}(\operatorname{groupLikeCoproduct}(b))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal preserves chronological multiplication componentwise.

**Theorem 1.3 (Coassociative group-like diagonal).**

$$\begin{gathered}\forall a:\\{}(\operatorname{fst}(\operatorname{groupLikeCoproduct}(a)), \operatorname{fst}(\operatorname{groupLikeCoproduct}(\operatorname{snd}(\operatorname{groupLikeCoproduct}(a)))), \operatorname{snd}(\operatorname{groupLikeCoproduct}(\operatorname{snd}(\operatorname{groupLikeCoproduct}(a)))))\\{}= (\operatorname{fst}(\operatorname{groupLikeCoproduct}(\operatorname{fst}(\operatorname{groupLikeCoproduct}(a)))), \operatorname{snd}(\operatorname{groupLikeCoproduct}(\operatorname{fst}(\operatorname{groupLikeCoproduct}(a)))), \operatorname{snd}(\operatorname{groupLikeCoproduct}(a))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_coassociative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Either order of iterating the diagonal produces three identical signature components.

**Theorem 1.4 (Left antipode cancellation).**

$$\forall a, \operatorname{signatureAntipode}(\operatorname{fst}(\operatorname{groupLikeCoproduct}(a))) \cdot \operatorname{snd}(\operatorname{groupLikeCoproduct}(a)) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_left_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the antipode leg by the identity leg yields the empty signature.

**Theorem 1.5 (Right antipode cancellation).**

$$\forall a, \operatorname{fst}(\operatorname{groupLikeCoproduct}(a)) \cdot \operatorname{signatureAntipode}(\operatorname{snd}(\operatorname{groupLikeCoproduct}(a))) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_right_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the identity leg by the antipode leg yields the empty signature.

**Theorem 1.6 (Reverse-and-negate realizes the antipode).**

$$\forall f, L, \operatorname{chronologicalSignature}(x \mapsto -\operatorname{f}(x), \operatorname{reverse}(L)) = \operatorname{signatureAntipode}(\operatorname{chronologicalSignature}(f, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing an event word and negating every observed value gives exactly the antipode of its chronological signature.

**Theorem 1.7 (Reverse-and-negate in logarithmic coordinates).**

$$\forall f, L, \operatorname{chronologicalLog}(\operatorname{chronologicalSignature}(x \mapsto -\operatorname{f}(x), \operatorname{reverse}(L))) = \operatorname{inverse}(\operatorname{chronologicalLog}(\operatorname{chronologicalSignature}(f, L))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_log_reverse_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After applying the logarithm, reverse-and-negate becomes coordinatewise negation.

**Theorem 1.8 (Involutive chronology reversal).**

$$\forall f, L, \operatorname{signatureAntipode}(\operatorname{chronologicalSignature}(x \mapsto -\operatorname{f}(x), \operatorname{reverse}(L))) = \operatorname{chronologicalSignature}(f, L).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the finite antipode after reverse-and-negate recovers the original signature.

**Theorem 1.9 (Reversal of concatenation).**

$$\begin{gathered}\forall f, P, S:\\{}\operatorname{chronologicalSignature}(x \mapsto -\operatorname{f}(x), \operatorname{reverse}(\operatorname{append}(P, S)))\\{}= \operatorname{signatureAntipode}(\operatorname{chronologicalSignature}(f, S)) \cdot \operatorname{signatureAntipode}(\operatorname{chronologicalSignature}(f, P)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse-and-negate sends concatenation to the reversed product of the two antipodes.

## References

- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_left_convolution`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.antipode_right_convolution`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_log_reverse_neg`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_append`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.chronological_signature_reverse_neg_involutive`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.groupLikeCoproduct`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_coassociative`
- Truth anchor: `D5/S3/Observer/Chronology/ChronologicalSignatureHopf.group_like_coproduct_mul`
- Dependency: [D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm](StepTwoChronologicalLogarithm.md)
