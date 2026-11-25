# Row residuals and the critical-mask energy budget

## Abstract

The row residual is controlled by a weighted amplitude energy. Centered spectral estimates give the posterior cap on six rows, and the scalar energy budget suffices for the sharp score bound.

**Definition 1.1 (The actual measurement amplitudes).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.measuredAmplitude`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.measuredAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An amplitude is an inner product with a computational or Fourier basis vector. Squared moduli give the two Born tables.

**Definition 1.2 (The squared row residual).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.rowResidual`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.rowResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row masses p and q ordered by the selected mask, the residual is ((1−c)p−(1+c)q)²/(p+q). Here c is the critical singular value. A common zero row contributes zero.

**Definition 1.3 (Weighted energy data).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.CriticalEnergyData`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.CriticalEnergyData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data contain the even and odd deficits, even leakage, aligned overlaps, the posterior caps outside the four light rows, and the weighted energy estimate with its two odd sectors.

**Theorem 1.4 (Centered reference overlap bounds).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.centered_overlap_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.centered_overlap_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit vectors at centered deficit below 0.075, total leakage is below 0.173. Each reference overlap is at least 0.909, and their sum is at least 1.9.

**Theorem 1.5 (The posterior cap on six heavy rows).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.centered_heavy_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.centered_heavy_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For aligned unit vectors at centered deficit below 0.075, a row outside the light set has minority mass at most 0.3 times its total mass. The light set consists of indices 1 and 4 in both bases. The estimate uses the row leverage and reference amplitude margin.

**Theorem 1.6 (The score bound from the energy data).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.score_le_of_energy_data`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.score_le_of_energy_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two unit vectors and a compatible sign mask, CriticalEnergyData supplies the residual estimate needed to bound the score by the exact cutoff (14 + 2√5)/5. The proof uses the common-zero convention and charges the even overlap mismatch to the positive odd sector and the even deficit.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.CriticalEnergyData`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.centered_heavy_posterior`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.centered_overlap_bounds`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.measuredAmplitude`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.rowResidual`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.score_le_of_energy_data`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign](CriticalSign.md)
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry](FourierGeometry.md)
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpParity](SharpParity.md)
