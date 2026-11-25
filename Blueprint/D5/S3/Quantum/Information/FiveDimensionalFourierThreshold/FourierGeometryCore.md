# Centered Fourier mask spectrum and covariance

## Abstract

The two-basis mask projection has an explicit spectrum on the centered critical representatives. Affine changes of residue labels preserve the measured amplitudes up to a shared unit phase.

**Definition 1.1 (Complex two-basis amplitudes).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryAmplitude`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The computational amplitude is the corresponding input coordinate. The Fourier amplitude is the normalized inverse QFT coordinate.

**Theorem 1.2 (Affine amplitude covariance).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryAmplitude_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryAmplitude_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit residue dilation followed by a computational shift and modulation induces the reciprocal dilation in the Fourier labels. The transported amplitude differs by a unimodular scalar depending only on its row, so the same phase transports both input states.

**Definition 1.3 (The two-basis mask operator).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryMask`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mask operator sums the rank-one orthogonal projections onto the selected basis columns.

**Theorem 1.4 (Mask quadratic and mixed forms).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.inner_geometryMask`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.inner_geometryMask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Its inner product with two states is the sum of the conjugate of the first measured amplitude times the second measured amplitude on the selected rows.

**Theorem 1.5 (Mask isometry covariance).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryMask_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryMask_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state isometry interchanges the original mask projection sum and the projection sum onto the permuted rows.

**Definition 1.6 (Normalized principal rays).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredRay`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredRay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each even or odd principal channel, the two extremal combinations are the sum and difference of positively phased unit principal vectors, divided by the square root of twice one plus or minus their overlap.

**Theorem 1.7 (Complementary principal overlap).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredProjectionDifference_ray`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredProjectionDifference_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of the two selected projections maps each principal ray onto the opposite-sign ray multiplied by the nonnegative complementary overlap.

**Theorem 1.8 (Exact centered mask spectra).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredEigenbasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredEigenbasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set c = √((7 + √5)/10), h = √((5 − √5)/10), σ = √((5 + √5)/10) and b = √((3 − √5)/10). The mask selecting the pair {2,3} in both bases has an orthonormal eigenbasis with eigenvalues 0, 1 ± b and 1 ± σ. Complementing the computational pair gives the rank-five mask with eigenvalues 1, 1 ± c and 1 ± h. The even principal channel corresponds to b in the first mask and c in the second.

**Theorem 1.9 (Spectrum transported to affine masks).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.affine_centeredEigenbasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.affine_centeredEigenbasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the affine state isometry to each centered eigenvector gives an eigenvector with the same eigenvalue for the corresponding transported mask.

**Theorem 1.10 (Complement mask spectrum).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.affine_centeredEigenbasis_compl_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.affine_centeredEigenbasis_compl_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full two-basis mask is twice the identity. The complement mask retains the transported eigenvectors and replaces each eigenvalue λ by 2 − λ.

**Theorem 1.11 (The Born mass in spectral coordinates).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredMask_mass_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredMask_mass_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the selected computational and Fourier Born probabilities is the sum of the squared eigenbasis coordinates weighted by the corresponding eigenvalues.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.affine_centeredEigenbasis_apply`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.affine_centeredEigenbasis_compl_apply`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredEigenbasis_apply`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredMask_mass_spectral`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredProjectionDifference_ray`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.centeredRay`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryAmplitude`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryAmplitude_affine`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryMask`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.geometryMask_affine`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.inner_geometryMask`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants](SharpConstants.md)
