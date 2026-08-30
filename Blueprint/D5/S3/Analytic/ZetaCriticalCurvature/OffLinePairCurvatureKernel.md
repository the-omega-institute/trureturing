# Off Line Pair Curvature Kernel

## Abstract

A reflection-paired logarithmic potential has a certified slope whose axis derivative is the off-line curvature dipole.

**Theorem 1.1 (Radial Quadratic Has Deriv At).**

$$\forall a: \mathbb{R}, y: \mathbb{R}, u: \mathbb{R},\\{}(HasDerivAt (radialQuadratic a y) (2 \times (u - a)) u).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_quadratic_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derivative of the radial quadratic.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Radial Log Potential Has Deriv At).**

$$\forall a: \mathbb{R}, y: \mathbb{R}, u: \mathbb{R},\\{}(radialQuadratic a y u \neq 0) \Rightarrow\\{}(HasDerivAt (radialLogPotential a y) (radialLogSlope a y u) u).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_log_potential_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed slope is the ordinary derivative whenever the local factor is nonzero.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Radial Log Slope Has Deriv At).**

$$\forall a: \mathbb{R}, y: \mathbb{R}, u: \mathbb{R},\\{}(radialQuadratic a y u \neq 0) \Rightarrow\\{}(HasDerivAt (radialLogSlope a y) ((y ^2 - (u - a) ^2) / (radialQuadratic a y u) ^2) u).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_log_slope_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derivative of the certified slope field.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Radial Quadratic Axis pos).**

$$\forall delta: \mathbb{R}, y: \mathbb{R},\\{}(0 < delta) \Rightarrow\\{}(0 < radialQuadratic delta y 0 \land 0 < radialQuadratic (-delta) y 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_quadratic_axis_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive displacement keeps both local factors nonzero at the fixed axis.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Off Line Pair Potential Has Deriv At Axis Zero).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R}, t: \mathbb{R},\\{}(0 < delta) \Rightarrow\\{}(HasDerivAt (\lambda u : \mathbb{R} \mapsto offLinePairPotential delta gamma u t) 0 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_potential_hasDerivAt_axis_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired potential has zero first normal derivative on the fixed axis.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Off Line Pair Slope Has Deriv At Axis).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R}, t: \mathbb{R},\\{}(0 < delta) \Rightarrow\\{}(HasDerivAt (\lambda u : \mathbb{R} \mapsto offLinePairSlope delta gamma u t) (offLinePairCurvatureKernel delta gamma t) 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_slope_hasDerivAt_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of the certified first-derivative field at the fixed axis is exactly the off-line curvature dipole.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Off Line Pair Curvature Center).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R},\\{}(delta \neq 0) \Rightarrow\\{}(offLinePairCurvatureKernel delta gamma gamma = -2 / delta ^2).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Center value of the dipole.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.8 (Off Line Pair Curvature Right Zero).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R},\\{}(delta \neq 0) \Rightarrow\\{}(offLinePairCurvatureKernel delta gamma (gamma + delta) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_right_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Right zero crossing at tangential offset delta.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.9 (Off Line Pair Curvature Left Zero).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R},\\{}(delta \neq 0) \Rightarrow\\{}(offLinePairCurvatureKernel delta gamma (gamma - delta) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_left_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left zero crossing at tangential offset -delta.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.10 (Off Line Pair Curvature Center neg).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R},\\{}(0 < delta) \Rightarrow\\{}(offLinePairCurvatureKernel delta gamma gamma < 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_center_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The center of a genuine off-axis pair is a negative curvature well.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.11 (Off Line Pair Curvature Reflection).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R}, y: \mathbb{R},\\{}(offLinePairCurvatureKernel delta gamma (gamma - y) = offLinePairCurvatureKernel delta gamma (gamma + y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dipole kernel is even in tangential displacement around its center.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_center`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_center_neg`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_left_zero`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_reflection`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_curvature_right_zero`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_potential_hasDerivAt_axis_zero`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.off_line_pair_slope_hasDerivAt_axis`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_log_potential_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_log_slope_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_quadratic_axis_pos`
- Truth anchor: `D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.radial_quadratic_hasDerivAt`
