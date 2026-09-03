# Point-Gap Finite-Scale Stability

## Abstract

A point-gap localizer stays invertible under a small relative position perturbation.

**Definition 1.1 (Position direction).**

Lean statement: `D5/S3/SpectralTopology/PointGapFiniteScaleStability.positionDirection`

*Formalization.* `D5/S3/SpectralTopology/PointGapFiniteScaleStability.positionDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shifted position observable defines a Hermitian block-diagonal direction on the doubled carrier.

**Definition 1.2 (Relative position perturbation).**

Lean statement: `D5/S3/SpectralTopology/PointGapFiniteScaleStability.relativePositionPerturbation`

*Formalization.* `D5/S3/SpectralTopology/PointGapFiniteScaleStability.relativePositionPerturbation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scaled position direction is measured in coordinates of the inverse zero-scale localizer.

**Definition 1.3 (Relative position factor).**

Lean statement: `D5/S3/SpectralTopology/PointGapFiniteScaleStability.relativePositionFactor`

*Formalization.* `D5/S3/SpectralTopology/PointGapFiniteScaleStability.relativePositionFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity plus the relative position perturbation is the factor controlling finite-scale invertibility.

**Theorem 1.4 (Explicit scale-budget stability).**

$$\operatorname{HasPointGap}(H, z) \land \lvert\operatorname{localizerZero}(X, H, x, z)^{-1}\rvert \cdot \lvert\kappa\rvert \cdot \lvert\operatorname{positionDirection}(X, x)\rvert < 1 \implies \operatorname{IsUnit}(\operatorname{localizer}(X, H, \kappa, x, z))$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/PointGapFiniteScaleStability.finite_scale_localizer_isUnit_of_scale_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hermitian position observable gives a Hermitian block-diagonal position direction, and the finite-scale localizer is the zero-scale localizer plus the scaled direction; under a point gap it factors through its zero-scale value and the relative position factor, making finite-scale invertibility equivalent to invertibility of that factor.

The relative perturbation norm is bounded by the inverse zero-scale norm times the scale and position-direction norms, and a perturbation of norm below one gives an invertible factor by the Neumann criterion; the explicit product bound is therefore a checkable sufficient stability budget, and combined with the frozen exact inertia a point gap supplies both half-dimensional chiral counts and invertibility throughout that budget.

## References

- Truth anchor: `D5/S3/SpectralTopology/PointGapFiniteScaleStability.finite_scale_localizer_isUnit_of_scale_bound`
- Truth anchor: `D5/S3/SpectralTopology/PointGapFiniteScaleStability.positionDirection`
- Truth anchor: `D5/S3/SpectralTopology/PointGapFiniteScaleStability.relativePositionFactor`
- Truth anchor: `D5/S3/SpectralTopology/PointGapFiniteScaleStability.relativePositionPerturbation`
- Dependency: [D5/S3/SpectralTopology/PointGapExactInertia](PointGapExactInertia.md)
