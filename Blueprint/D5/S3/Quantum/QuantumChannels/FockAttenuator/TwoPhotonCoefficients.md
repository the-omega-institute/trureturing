# Exact two-photon occupation amplitudes

## Abstract

The closed balanced two-photon transition coefficient holds for arbitrary completed Fock inputs.

**Theorem 1.1 (The full occupation coefficient formula).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/TwoPhotonCoefficients.balanced_two_photon_occupation_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/TwoPhotonCoefficients.balanced_two_photon_occupation_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N=i+j>=2. At transmissivity one half and environment occupation two, the actual output coordinate j,i is a(N-2) times sqrt(choose(N,i)/2^N) times (((i-j)^2-N)/sqrt(2*N*(N-1))). The occupation difference and the two subtractions in this expression are in Real, rather than truncated Natural subtraction. All square-root factors are positive where a denominator occurs. For N<2 the earlier occupation theorem gives zero.

The proof starts with the existing finite beamSplitter occupation expansion. A guarded binomial reciprocity identity, proved from factorial formulas, handles all boundary occupations before the three environment terms are combined. Their alternating sum gives the exact quadratic factor (i-j)^2-N. Positive square-root identities and the full factorial normalization then give the stated closed amplitude.

The arbitrary-support input factor a(N-2) comes from equality of continuous linear coordinate maps on the whole completed Hilbert space. Finite-support approximation, a numerical cutoff, assigned matrix entries and an assumed analytic bridge are not premises. This coefficient formula and the independently proved completed kernel identity describe the same existing physical channel.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/TwoPhotonCoefficients.balanced_two_photon_occupation_coefficient`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/OccupationCoefficients](OccupationCoefficients.md)
