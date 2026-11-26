# Reflecting heat saddle density

## Abstract

The reflecting heat saddle determines the density of the equal-mass bins and the multiplier's imaginary potential.

**Theorem 1.1 (Unique positive saddle radius).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.existsUnique_saddle_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.existsUnique_saddle_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The angular average of the reciprocal saddle radius is continuous and strictly decreasing on the positive half-line. The polynomial bounds at small and large radii bracket half the window parameter, so the intermediate value theorem gives the unique radius used by the physical estimate.

**Theorem 1.2 (Evaluation of the imaginary potential).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.imaginaryPotential_eval_at_saddle`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.imaginaryPotential_eval_at_saddle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the potential yields an integral against the saddle density. Evaluating the radial integral and exchanging it with the angular average gives the weighted resolvent. The evaluated expression and the potential have this same derivative and both vanish at zero.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.existsUnique_saddle_radius`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatSaddleDensity.imaginaryPotential_eval_at_saddle`
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct](ReflectingHeatCanonicalProduct.md)
