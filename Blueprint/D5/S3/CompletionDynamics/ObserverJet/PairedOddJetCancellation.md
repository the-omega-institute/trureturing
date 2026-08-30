# Paired Odd Jet Cancellation

## Abstract

Reflection pairing cancels odd linear jets while preserving quadratic information in the even channel.

**Theorem 1.1 (Even Add Odd eq).**

$$\forall f: \mathbb{R} \to \mathbb{R}, h: \mathbb{R},\\{}(evenChannel f h + oddChannel f h = f h).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.even_add_odd_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every profile decomposes exactly into its paired even and odd channels.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Even Channel neg).**

$$\forall f: \mathbb{R} \to \mathbb{R}, h: \mathbb{R},\\{}(evenChannel f (-h) = evenChannel f h).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.even_channel_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired even channel is invariant under reflection.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Odd Channel neg).**

$$\forall f: \mathbb{R} \to \mathbb{R}, h: \mathbb{R},\\{}(oddChannel f (-h) = -oddChannel f h).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.odd_channel_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired odd channel changes sign under reflection.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Linear Jet Even Channel Zero).**

$$\forall v: \mathbb{R}, h: \mathbb{R},\\{}(evenChannel (\lambda u : \mathbb{R} \mapsto v \times u) h = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.linear_jet_even_channel_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A first-order signed jet vanishes after pairing in the even channel.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Linear Jet Odd Channel).**

$$\forall v: \mathbb{R}, h: \mathbb{R},\\{}(oddChannel (\lambda u : \mathbb{R} \mapsto v \times u) h = v \times h).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.linear_jet_odd_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same first-order jet is retained exactly in the odd channel.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Reflected Tangent Square).**

$$\forall v: \mathbb{R},\\{}((-v) ^2 = v ^2).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.reflected_tangent_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring a reflected tangent removes its sign.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Quadratic Jet Even Channel).**

$$\forall v: \mathbb{R}, h: \mathbb{R},\\{}(evenChannel (\lambda u : \mathbb{R} \mapsto (v \times u) ^2) h = (v \times h) ^2).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.quadratic_jet_even_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quadratic jet survives reflection pairing in the even channel.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.8 (Quadratic Jet Odd Channel Zero).**

$$\forall v: \mathbb{R}, h: \mathbb{R},\\{}(oddChannel (\lambda u : \mathbb{R} \mapsto (v \times u) ^2) h = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.quadratic_jet_odd_channel_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quadratic jet has zero odd component.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.9 (Paired Tangent Average Zero).**

$$\forall v: \mathbb{R},\\{}((v + (-v)) / 2 = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.paired_tangent_average_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct vector-pair version of first-order cancellation.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.10 (Paired Tangent Second Moment).**

$$\forall v: \mathbb{R},\\{}((v ^2 + (-v) ^2) / 2 = v ^2).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.paired_tangent_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second moment of a reflected tangent pair is the original square.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.even_add_odd_eq`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.even_channel_neg`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.linear_jet_even_channel_zero`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.linear_jet_odd_channel`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.odd_channel_neg`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.paired_tangent_average_zero`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.paired_tangent_second_moment`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.quadratic_jet_even_channel`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.quadratic_jet_odd_channel_zero`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.reflected_tangent_square`
