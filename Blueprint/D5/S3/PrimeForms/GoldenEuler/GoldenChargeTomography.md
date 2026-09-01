# Golden Charge Tomography

## Abstract

Neutral and quadratic charge channels invert exactly to split and inert channels by the C2 Fourier transform.

**Theorem 1.1 (The Split Channel Is Reconstructed Exactly).**

$$\forall split: \mathbb{R}, inert: \mathbb{R},\\{}(splitFromChannels(\operatorname{neutralChannel}\left(split, inert\right), \operatorname{chargeChannel}\left(split, inert\right)) = split).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_channel_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding the neutral and signed charge channels isolates twice the split component.

Division by two gives exact finite Fourier inversion and requires no analytic assumptions.

**Theorem 1.2 (The Inert Channel Is Reconstructed Exactly).**

$$\forall split: \mathbb{R}, inert: \mathbb{R},\\{}(inertFromChannels(\operatorname{neutralChannel}\left(split, inert\right), \operatorname{chargeChannel}\left(split, inert\right)) = inert).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.inert_channel_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the signed charge channel from the neutral channel isolates twice the inert component.

The identity is purely algebraic and does not make a statement about Dirichlet series or zeros.

**Theorem 1.3 (The Indicators Partition Unit Mass).**

$$\forall charge: \mathbb{R},\\{}(\operatorname{splitIndicator}\left(charge\right) + \operatorname{inertIndicator}\left(charge\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_add_inert_indicator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive and negative charge indicators add to one for every real charge value.

This partition identity is algebraic; it does not require the charge to equal plus or minus one.

**Theorem 1.4 (The Signed Indicator Difference Recovers Charge).**

$$\forall charge: \mathbb{R},\\{}(\operatorname{splitIndicator}\left(charge\right) - \operatorname{inertIndicator}\left(charge\right) = charge).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_sub_inert_indicator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split indicator minus the inert indicator reproduces the original real charge.

Together with the sum identity, this records the two-coordinate inverse transform only.

**Theorem 1.5 (Positive Charge Selects the Split Indicator).**

$$(\operatorname{splitIndicator}\left(1\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_indicator_pos_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At charge plus one, the split indicator has value one.

The endpoint evaluation identifies the split channel without asserting a classification of inputs.

**Theorem 1.6 (Positive Charge Vanishes in the Inert Indicator).**

$$(\operatorname{inertIndicator}\left(1\right) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.inert_indicator_pos_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At charge plus one, the inert indicator has value zero.

This is the complementary endpoint evaluation to the positive split indicator.

**Theorem 1.7 (Negative Charge Vanishes in the Split Indicator).**

$$(\operatorname{splitIndicator}\left(-1\right) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_indicator_neg_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At charge minus one, the split indicator has value zero.

The theorem evaluates the finite indicator and introduces no local Euler hypothesis.

**Theorem 1.8 (Negative Charge Selects the Inert Indicator).**

$$(\operatorname{inertIndicator}\left(-1\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.inert_indicator_neg_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At charge minus one, the inert indicator has value one.

This completes the two endpoint evaluations of the charge-channel transform.

## References

- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.inert_channel_reconstruction`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.inert_indicator_neg_charge`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.inert_indicator_pos_charge`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_add_inert_indicator`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_channel_reconstruction`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_indicator_neg_charge`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_indicator_pos_charge`
- Truth anchor: `D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography.split_sub_inert_indicator`
