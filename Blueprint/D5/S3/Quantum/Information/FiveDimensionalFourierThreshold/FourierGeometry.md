# Centered Fourier row masses and critical mask orbit

## Abstract

The exact principal-ray measurements on the centered masks give individual row estimates. Every critical pair of differences is reached through an affine state isometry.

**Theorem 1.1 (Fourier pair row masses).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRay_fourier_pair_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRay_fourier_pair_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a principal ray of overlap r and sign s = ±1, each of its two selected Fourier pair rows carries the probability (1 + s r)/4, in either centered mask rank.

**Theorem 1.2 (Omitted computational pair row masses).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_ray_standard_pair_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_ray_standard_pair_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the rank-five mask the computational pair is omitted. Each of its two rows carries probability (1 − s r)/4 for the principal ray with overlap r and sign s.

**Theorem 1.3 (Odd principal rays at the central row).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRay_odd_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRay_odd_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In either rank, both odd principal rays have zero amplitude in computational row zero and Fourier row zero.

**Theorem 1.4 (Rank-five even principal masses at row zero).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_ray_zero_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_ray_zero_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z = (7 − √5)/11 and c = √((7 + √5)/10). On the even principal ray with sign s, the zero rows carry masses (1 + s c)Z/2 in the computational basis and (1 − s c)Z/2 in the Fourier basis.

**Theorem 1.5 (The middle eigenvector's central mass).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_middle_zero_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_middle_zero_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the rank-five mask the eigenvector of eigenvalue one carries central row mass 1 − Z in each basis, as the other four eigenvectors account for the remaining contribution.

**Theorem 1.6 (The middle eigenvector vanishes on the centered pair).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_middle_pair_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_middle_pair_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The middle eigenvector of the rank-five mask has zero probability on both pair rows in each of the computational and Fourier bases.

**Theorem 1.7 (Weighted estimate for a single measured row).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.geometryAmplitude_sq_le_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.geometryAmplitude_sq_le_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite sum of vectors with complex coefficients and positive weights g, the squared amplitude on a fixed row is at most the sum of vector row masses divided by g, multiplied by the sum of squared coefficient moduli weighted by g. This retains complex vector amplitudes and allows the weights to be the exact spectral gaps.

**Theorem 1.8 (Affine orbit of the critical masks).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.criticalMasks_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.criticalMasks_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the product of the two ordered pair differences in Z/5Z is ±1, a single dilation, standard shift and Fourier modulation transports the centered pairs {2,3} to those pairs. The same transformation transports the centered four-row mask and the centered five-row mask, along with the complementary five-row orientation.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_middle_pair_mass`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_middle_zero_mass`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_ray_standard_pair_mass`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRankFive_ray_zero_mass`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRay_fourier_pair_mass`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.centeredRay_odd_zero`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.criticalMasks_affine`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.geometryAmplitude_sq_le_weighted`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore](FourierGeometryCore.md)
