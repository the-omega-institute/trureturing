# Harmonic overlap from finite threshold masks

## Abstract

The score is four minus four times the harmonic deficit when each of the two laws has mass two.

**Definition 1.1 (Triangular discrimination on a finite table).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.score`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.score` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each row contributes its squared mass difference divided by its total mass. A common zero row contributes zero.

**Definition 1.2 (The two mass gaps).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.SpectralMaskGaps`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.SpectralMaskGaps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mask larger than half the table has mass at least A. A mask of exactly half the table has mass at least E.

**Theorem 1.3 (The harmonic deficit bound).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.overlap_lower_bound_of_mask_gaps`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.overlap_lower_bound_of_mask_gaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row score minimizing the quadratic loss is q/(p+q). Integrating over threshold masks gives a density bounded below by the minimum of 2At, 2E, and 2A(1-t). Integrating this minimum gives 2E − 2E²/A.

**Theorem 1.4 (The score bound for two normalized laws).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.score_upper_bound_of_mask_gaps`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.score_upper_bound_of_mask_gaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The score is four minus four times the harmonic deficit when each of the two laws has mass two.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.SpectralMaskGaps`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.overlap_lower_bound_of_mask_gaps`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.score`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.score_upper_bound_of_mask_gaps`
