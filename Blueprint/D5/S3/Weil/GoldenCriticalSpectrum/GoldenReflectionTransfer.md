# Golden Reflection Transfer

## Abstract

Reflection-paired golden gains are globally balanced, while pointwise neutrality occurs exactly at zero normal displacement.

**Theorem 1.1 (Every Golden Transfer Gain Is Positive).**

$$\forall \delta: \mathbb{R},\\{}(0 < \operatorname{goldenTransferGain}\left(\delta\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.golden_transfer_gain_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transfer gain is a real exponential and is strictly positive for every real normal displacement.

This sign statement does not require the displacement to arise from a spectral point.

**Theorem 1.2 (Reflected Displacement Gives Reciprocal Gain).**

$$\forall \delta: \mathbb{R},\\{}(\operatorname{goldenTransferGain}\left(-\delta\right) = {\operatorname{goldenTransferGain}\left(\delta\right)}^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.golden_transfer_gain_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negating a normal displacement turns its exponential golden gain into the reciprocal gain.

The identity expresses reflection symmetry pointwise and makes no neutrality claim.

**Theorem 1.3 (A Reflected Gain Pair Has Product One).**

$$\forall \delta: \mathbb{R},\\{}(\operatorname{goldenTransferGain}\left(\delta\right) \times \operatorname{goldenTransferGain}\left(-\delta\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.reflected_transfer_product_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every displacement, its gain and the gain at the negative displacement multiply to one.

This determinant-like paired balance holds even when neither member has unit gain.

**Theorem 1.4 (Unit Gain Characterizes Zero Displacement).**

$$\forall \delta: \mathbb{R},\\{}((\operatorname{goldenTransferGain}\left(\delta\right) = 1) \Leftrightarrow (\delta = 0)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.golden_transfer_gain_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden transfer gain equals one exactly when the real normal displacement is zero.

Strict positivity of the golden period makes the exponential coordinate injective at the unit value.

**Theorem 1.5 (Both Reflected Gains Are Unit Exactly on the Fixed Axis).**

$$\forall \delta: \mathbb{R},\\{}(((\operatorname{goldenTransferGain}\left(\delta\right) = 1) \land (\operatorname{goldenTransferGain}\left(-\delta\right) = 1)) \Leftrightarrow (\delta = 0)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.reflected_pair_pointwise_neutral_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A displacement and its reflection both have unit gain exactly at zero displacement.

The conjunction enforces pointwise neutrality of both members, which is stronger than their automatic product balance.

**Theorem 1.6 (Paired Balance Is Strictly Weaker Than Pointwise Neutrality).**

$$((\operatorname{goldenTransferGain}\left(1\right) \times \operatorname{goldenTransferGain}\left(-1\right) = 1) \land (\operatorname{goldenTransferGain}\left(1\right) \neq 1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.paired_balance_strictly_weaker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At displacement one, the reflected gain pair still has product one while the positive-displacement gain is not one.

This explicit witness separates global paired balance from the pointwise unit-gain condition.

## References

- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.golden_transfer_gain_eq_one_iff`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.golden_transfer_gain_neg`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.golden_transfer_gain_pos`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.paired_balance_strictly_weaker`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.reflected_pair_pointwise_neutral_iff`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer.reflected_transfer_product_one`
- Dependency: [D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius](GoldenCriticalRadius.md)
