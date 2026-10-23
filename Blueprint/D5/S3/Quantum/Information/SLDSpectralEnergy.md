# Hermitian SLD energy

## Abstract

Density matrices and spectral energy of symmetric logarithmic derivatives.

**Definition 1.1 (Density matrices).**

Lean statement: `D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity`

*Formalization.* `D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A density matrix is a positive semidefinite complex matrix with trace one on an arbitrary finite index type.

**Theorem 1.2 (Energy in a specified diagonal basis).**

Lean statement: `D5/S3/Quantum/Information/SLDSpectralEnergy.diagonal_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SLDSpectralEnergy.diagonal_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real diagonal D with entries w, a Hermitian L satisfying LD+DL=2B has real trace(LDL) equal to the sum over ordered pairs of 2 times the squared modulus of B(i,j), divided by w(i)+w(j). Real division gives zero when the denominator vanishes. The statement allows any real diagonal; positivity is not needed for this algebraic identity.

**Theorem 1.3 (Energy in an eigenbasis).**

Lean statement: `D5/S3/Quantum/Information/SLDSpectralEnergy.spectral_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SLDSpectralEnergy.spectral_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive semidefinite rho and every Hermitian L satisfying L rho+rho L=2B, real trace(L rho L) equals spectralQFI(rho,B). The proof conjugates the equation into the eigenvector basis and applies the diagonal energy identity. This is the same spectralQFI defined in ActualPureQubitGeometry, including its convention at zero eigenvalue sums.

## References

- Truth anchor: `D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity`
- Truth anchor: `D5/S3/Quantum/Information/SLDSpectralEnergy.diagonal_energy`
- Truth anchor: `D5/S3/Quantum/Information/SLDSpectralEnergy.spectral_energy`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
