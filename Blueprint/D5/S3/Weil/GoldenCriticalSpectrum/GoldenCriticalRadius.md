# Golden Critical Radius

## Abstract

Golden exponential radial coordinates send the critical line to the unit radius and completed reflection to reciprocal radius.

**Theorem 1.1 (The Golden Critical Radius Is Positive).**

$$\forall s: \mathbb{C},\\{}(0 < \operatorname{goldenCriticalRadius}\left(s\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.golden_critical_radius_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden critical radius is a real exponential of the scaled normal offset and is therefore strictly positive at every complex point.

Positivity concerns only the coordinate itself and supplies no information about the location of zeros.

**Theorem 1.2 (Critical Reflection Negates the Normal Offset).**

$$\forall s: \mathbb{C},\\{}(\operatorname{criticalOffset}\left(\operatorname{criticalReflection}\left(s\right)\right) = -\operatorname{criticalOffset}\left(s\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.critical_offset_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection across the critical line reverses the signed real displacement from one half.

The equality is an exact coordinate calculation and does not depend on a function or a zero set.

**Theorem 1.3 (Unit Golden Radius Characterizes the Critical Line).**

$$\forall s: \mathbb{C},\\{}((\operatorname{goldenCriticalRadius}\left(s\right) = 1) \Leftrightarrow (s.re = \frac{1}{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.golden_critical_radius_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex point has golden critical radius one exactly when its real part equals one half.

This equivalence characterizes the coordinate locus only; it does not prove that any specified spectrum lies there.

**Theorem 1.4 (Critical Reflection Takes Radius to Its Reciprocal).**

$$\forall s: \mathbb{C},\\{}(\operatorname{goldenCriticalRadius}\left(\operatorname{criticalReflection}\left(s\right)\right) = {\operatorname{goldenCriticalRadius}\left(s\right)}^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.golden_critical_radius_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negating the normal offset changes the exponential radius into the reciprocal of the original radius.

The result applies pointwise to every complex number, independently of spectral or functional-equation hypotheses.

**Theorem 1.5 (Every Reflected Pair Has Unit Radius Product).**

$$\forall s: \mathbb{C},\\{}(\operatorname{goldenCriticalRadius}\left(s\right) \times \operatorname{goldenCriticalRadius}\left(\operatorname{criticalReflection}\left(s\right)\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.reflected_radius_product_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive radius of a point multiplied by the reciprocal radius of its reflection is exactly one.

Paired balance does not imply that either individual radius is one.

**Theorem 1.6 (A Set Is Critical Exactly When All Its Radii Are Unit).**

$$\forall Z: \operatorname{Set}\left(\mathbb{C}\right),\\{}((\forall s: \mathbb{C}, (s \in Z) \Rightarrow (s.re = \frac{1}{2})) \Leftrightarrow (\forall s: \mathbb{C}, (s \in Z) \Rightarrow (\operatorname{goldenCriticalRadius}\left(s\right) = 1))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.all_critical_iff_all_unit_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of a complex set lies on the critical line exactly when every member has golden radius one.

Both universal statements retain set membership as a premise, so nothing is claimed about points outside the chosen set.

## References

- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.all_critical_iff_all_unit_radius`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.critical_offset_reflection`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.golden_critical_radius_eq_one_iff`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.golden_critical_radius_pos`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.golden_critical_radius_reflection`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius.reflected_radius_product_one`
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle](../../Observer/GoldenPrimeCircle/GoldenScaleCircle.md)
