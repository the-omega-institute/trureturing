# Signed qubit profiles

## Abstract

Signed qubit profiles

**Definition 1.1 (Signed contrast).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.contrast`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/SignedProfile.contrast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite family of qubit amplitudes, sum the outer products of the amplitudes with their conjugates using arbitrary real coefficients.

**Definition 1.2 (Squared overlap).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.overlap`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/SignedProfile.overlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared modulus of the Hermitian inner product of two amplitudes in the family.

**Definition 1.3 (Signed overlap discriminant).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq`

*Formalization.* `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract four times the sum of weighted overlap deficits over increasing index pairs from the square of the total weight. For unit preparations, this is the squared spectral gap of the contrast.

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

Compare two unit families at fixed weights and with all increasing-pair overlaps equal except possibly at the selected pair. The second positive-part trace is at least the first whenever the corresponding weight product times (the second squared overlap minus the first squared overlap) is nonnegative.

**Theorem 1.7 (Minimum overlap at fixed coordinate magnitudes).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.phase_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/SignedProfile.phase_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any amplitudes with coordinate magnitudes (cos θ, sin θ) and (sin φ, cos φ), the squared overlap is at least sin²(φ−θ) by the reverse triangle inequality for the two terms of the complex inner product. The real amplitudes (cos θ, sin θ) and (sin φ, −cos φ) are unit and have squared overlap sin²(φ−θ) for all angles. When all four prescribed magnitudes are nonnegative, for example when θ and φ lie in [0, π/2], these amplitudes have the prescribed magnitudes and attain the bound.

**Theorem 1.8 (Maximum profile at fixed coordinate magnitudes).**

Lean statement: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast_isGreatest_opposite_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast_isGreatest_opposite_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix e₀ = (1, 0) and angles θ, φ in [0, π/2]. For three real weights with a₀a₂ ≤ 0, the unit triple ((cos θ, sin θ), e₀, (sin φ, −cos φ)) belongs to the domain and its positive-part trace bounds that of every unit triple (u, e₀, v) with coordinate magnitudes (cos θ, sin θ) and (sin φ, cos φ). The two reference overlaps are the squared first-coordinate magnitudes, cos² θ and sin² φ. The minimum-overlap theorem minimizes the outer squared overlap, so the signed single-overlap comparison gives the upper bound. This is the pointwise fixed-basis step in the Gibbs-record upper bound. Changing to the reference basis, integrating the profile, and verifying the global certificate are separate steps.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.contrast`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.gapSq_eq_trace_det`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.overlap`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.phase_minimum`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast_isGreatest_opposite_phase`
- Truth anchor: `D5/S3/Quantum/Divergence/Qubit/SignedProfile.trace_posPart_contrast_le_of_pair`
- Dependency: [D5/S3/Observer/BornReduction](../../../Observer/BornReduction.md)
