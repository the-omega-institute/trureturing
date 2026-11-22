# Signed qubit profiles

## Abstract

Signed qubit profiles

**Definition 1.1 (Signed contrast).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.contrast`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/SignedProfile.contrast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite family of qubit amplitudes, sum their rank-one matrices with arbitrary real coefficients.

**Definition 1.2 (Squared overlap).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.overlap`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/SignedProfile.overlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared modulus of the Hermitian inner product of two amplitudes in the family.

**Definition 1.3 (Squared spectral gap).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract four times the sum of weighted overlap deficits over increasing index pairs from the square of the total weight.

**Theorem 1.4 (Signed overlap expansion).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq_eq_trace_det`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq_eq_trace_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit preparations, the squared gap is the square of the total weight minus four times the real determinant of the contrast. Expanding the trace of the square gives an ordered sum of weighted overlaps. The overlap deficits have zero diagonal and are symmetric, so each increasing pair contributes twice.

**Theorem 1.5 (Trace of the positive part).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real weights and unit preparations, the trace of the positive part is half the sum of the total weight and the larger of its absolute value and the square root of the squared gap. The proof applies the positive part to each of the two eigenvalues.

**Theorem 1.6 (Comparison at a single overlap).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast_le_of_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast_le_of_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare two unit families at fixed weights and with all increasing-pair overlaps equal except possibly at the selected pair. The second profile is at least the first whenever the corresponding weight product times the second overlap minus the first overlap is nonnegative.

**Theorem 1.7 (Three-class discriminant).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq_fin_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq_fin_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With squared overlaps (1−X,Y,Z) in pair order (1,2), (1,3), (2,3), the discriminant is (a₃−a₁−a₂)² + 4(−a₁a₂X+a₁a₃Y+a₂a₃Z). This is the polynomial entering the Gibbs-record certificate.

**Theorem 1.8 (Minimum overlap at fixed coordinate magnitudes).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.phase_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/SignedProfile.phase_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For amplitudes with coordinate magnitudes (cos θ,sin θ) and (sin φ,cos φ), the squared overlap is at least sin²(φ−θ). The real amplitudes (cos θ,sin θ) and (sin φ,−cos φ) are unit and attain equality. The lower bound follows by applying the reverse triangle inequality to the two terms of the complex inner product.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.contrast`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq_eq_trace_det`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq_fin_three`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.overlap`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.phase_minimum`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast_le_of_pair`
