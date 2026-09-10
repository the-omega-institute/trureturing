# OccupationConcentration

## Abstract

Uniform complex response bounds control actual discrete Gibbs fluctuations.

**Definition 1.1 (densityMeanSquare).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationConcentration.densityMeanSquare`

*Formalization.* `D5/S3/HardCoreHolomorphic/OccupationConcentration.densityMeanSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mean-square fluctuation of the actual occupation density. The weights are point masses of the existing Gibbs PMF. Empty domains are excluded whenever this expression is interpreted as a density.

**Theorem 1.2 (density mean square eq).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_mean_square_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_mean_square_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rescaling the actual centered moment gives variance divided by volume squared. No independent-site assumption is used.

**Theorem 1.3 (grid density mean square bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_mean_square_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_mean_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density is mean-square concentrated around its own finite-volume mean, with a volume-independent coefficient. This makes no assertion that those means have a common infinite-volume limit.

**Definition 1.4 (densityDeviationMass).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationConcentration.densityDeviationMass`

*Formalization.* `D5/S3/HardCoreHolomorphic/OccupationConcentration.densityDeviationMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual Gibbs event probability, written as the finite sum of point masses. It is not a probability assigned to complex normalized weights.

**Theorem 1.5 (density deviation mass bounds).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_mass_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_mass_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event expression is a number between zero and one, by positivity and normalization of the actual finite probability law.

**Theorem 1.6 (density deviation le second moment).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_le_second_moment`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_le_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite Chebyshev estimate on this exact Gibbs sample space. The event threshold is positive; the density denominator is not used for division in this proof, so the algebraic inequality also covers the empty domain.

**Theorem 1.7 (grid density deviation bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_deviation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_deviation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-size concentration around the actual finite-volume mean. The constant comes from the proved analytic variance bound, not a supplied concentration hypothesis. It becomes O(1/volume) for any fixed threshold.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationConcentration.densityDeviationMass`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationConcentration.densityMeanSquare`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_le_second_moment`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_mass_bounds`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationConcentration.density_mean_square_eq`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_deviation_bound`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_mean_square_bound`
- Dependency: [D5/S3/HardCoreHolomorphic/LinearVolumeVariance](LinearVolumeVariance.md)
