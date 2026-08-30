# Massless Holonomy Determinant

## Abstract

The reflected massless holonomy zeta has a scale-free sine determinant.

**Theorem 1.1 (The reflected Hurwitz sum vanishes at zero).**

$$\forall alpha \in \mathbb{R},\; \left(0 < \alpha \land \alpha < 1\right) \Rightarrow \operatorname{holonomyHurwitzSum}(\alpha, 0) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_hurwitz_sum_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a holonomy strictly between zero and one, the two reflected Hurwitz sectors form twice the even Hurwitz zeta value, which is zero at the origin.

**Theorem 1.2 (The determinant is independent of an overall scale).**

$$\forall alpha \in \mathbb{R}, scale \in \mathbb{R},\; \left(0 < \alpha \land \alpha < 1\right) \Rightarrow \operatorname{zetaRegularizedDeterminant}(\operatorname{scaledSpectralZeta}(scale, \operatorname{holonomyHurwitzSum}(\alpha))) = \operatorname{masslessHolonomyDeterminant}(\alpha)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_determinant_scale_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the exponential scale factor produces a term multiplied by the reflected zeta value at zero. The preceding vanishing result therefore removes it for every real scale parameter.

**Theorem 1.3 (The massless determinant is the sine chord).**

$$\forall alpha \in \mathbb{R},\; \left(\left(0 < \alpha \land \alpha < 1\right) \land \operatorname{HasReflectedHurwitzDerivativeAtZeroFormula}(\alpha)\right) \Rightarrow \operatorname{masslessHolonomyDeterminant}(\alpha) = 2 \times \operatorname{sin}(\pi \times \alpha)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.massless_holonomy_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming the reflected Lerch derivative formula missing from the pinned library, Euler reflection converts the zeta derivative to the dimensionless value two times sine of pi alpha.

**Theorem 1.4 (The sine value is the unit-circle chord length).**

$$\forall alpha \in \mathbb{R},\; \left(0 \le \alpha \land \alpha \le 1\right) \Rightarrow \operatorname{holonomyChordLength}(\alpha) = 2 \times \operatorname{sin}(\pi \times \alpha)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_sine_eq_chord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha in the closed unit interval, the norm of the difference from one to the unit-circle point with angle two pi alpha is exactly two times sine of pi alpha.

**Theorem 1.5 (The chord identity needs both interval bounds).**

$$\operatorname{holonomyChordLength}(-\frac{1}{2}) \ne 2 \times \operatorname{sin}(\pi \times -\frac{1}{2}) \land \operatorname{holonomyChordLength}(\frac{3}{2}) \ne 2 \times \operatorname{sin}(\pi \times \frac{3}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.chord_interval_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At alpha minus one half and three halves, the sine expression is negative while the norm defining the chord is positive. The two concrete witnesses separately cross the lower and upper bounds.

**Theorem 1.6 (Both interval endpoints violate the sine formula).**

$$\operatorname{masslessHolonomyDeterminant}(0) \ne 2 \times \operatorname{sin}(\pi \times 0) \land \operatorname{masslessHolonomyDeterminant}(1) \ne 2 \times \operatorname{sin}(\pi \times 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_interval_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At alpha zero and one the sine side vanishes, while a complex exponential is never zero. These named endpoint witnesses justify excluding both boundaries.

**Theorem 1.7 (Vanishing at zero alone does not determine the determinant).**

$$\operatorname{zeroZeta}(0) = 0 \land \operatorname{zetaRegularizedDeterminant}(zeroZeta) \ne 2 \times \operatorname{sin}(\pi \times \frac{1}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.derivative_formula_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-zero mock zeta vanishes at zero but has regularized determinant one, not the value two obtained at alpha one half. Thus derivative data cannot be replaced by zero-value data alone.

## References

- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.chord_interval_is_necessary`
- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.derivative_formula_is_necessary`
- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_determinant_scale_invariant`
- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_hurwitz_sum_at_zero`
- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_interval_is_necessary`
- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.holonomy_sine_eq_chord_length`
- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.massless_holonomy_determinant`
