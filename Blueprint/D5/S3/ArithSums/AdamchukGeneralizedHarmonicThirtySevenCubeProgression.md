# Adamchuk's A116184 progression

## Abstract

Every exponent in Adamchuk's progression gives a generalized harmonic numerator divisible by 37 cubed.

**Definition 1.1 (The generalized harmonic sum).**

$$\forall n \in \mathbb{N},\; H\left(n\right) = \sum_{j \in Finset.Icc\left(1, 36\right)} \frac{(1: \mathbb{Q})}{(j: \mathbb{Q})^{n}}$$

*Formalization.* `D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.H` (`✓ std3`).

*Citation.* Alexander Adamchuk (2007). *OEIS A116184, Numbers n such that 37^3 divides the numerator of generalized harmonic number H(36,n) = Sum[ 1/k^n, {k,1,36} ]*. URL: <https://oeis.org/A116184>.

*Commentary.*

This is the generalized harmonic number H(36, n) of OEIS A116184; Rat.num below is the reduced numerator.

**Theorem 1.2 (Cubic divisibility along the progression).**

$$\forall k \in \mathbb{N},\; (37^{3}: \mathbb{Z}) \mid num\left(H\left(3 + 36 \cdot k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.adamchuk_a116184` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a116184-generalized-harmonic-thirty-seven-cube-progression` (proved) by `D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.adamchuk_a116184`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a116184-generalized-harmonic-thirty-seven-cube-progression","declaration_gid":"D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.adamchuk_a116184","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Cubic nilpotence gives a third-order recurrence. Three initial certificates and induction make every recurrence value vanish, and the numerator bridge transfers that divisibility to the reduced numerator of the harmonic sum.

## References

- Truth anchor: `D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.H`
- Truth anchor: `D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.adamchuk_a116184`
