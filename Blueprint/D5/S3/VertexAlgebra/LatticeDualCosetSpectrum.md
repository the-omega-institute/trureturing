# Actual Algebraic Dual-Coset Point Spectrum

## Abstract

Actual Algebraic Dual-Coset Point Spectrum

The spectrum is the algebraic point spectrum of the ACTUAL original-omega moduleL_0 on the full finite-support carrier. H is a two-sided inverse of the original complex Gram matrix; beta is integral; mu is rational and G_Q mu=beta. Positive original real Gram constructs a nonnegative attained minimum h and finite fibers. Every eigenvalue is h+n for a natural n. Equality with the full set h+N requires positive rank, where frequency-one oscillators realize every n. In rank zero the carrier is the existing nonzero vacuum line, the original omega is zero, the only eigenvalue is zero, and the constructed h is zero. Bottom fibers consist of all minimizing charges and zero oscillator exponent. For the rank-one even Gram [2] with mu=1/2, h=1/4 is attained at two distinct charges. Virasoro modes send energy e to e-m and positive modes annihilate the entire bottom space. No generation by Virasoro modes, analytic Hilbert spectrum, classification, fusion, complete CFT, Monster, string theory or AdS/CFT result is asserted.

**Theorem 1.1 (point spectrum subset).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.point_spectrum_subset`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.point_spectrum_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any nonzero actual eigenvector has a nonzero actual basis coefficient, which forces its COMPLEX eigenvalue to equal cast(h+n) for a natural n.

**Theorem 1.2 (positive rank point spectrum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.positive_rank_point_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.positive_rank_point_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When rank(D)>0, the actual algebraic point spectrum is exactly cast(h+N). A frequency-one oscillator on a minimizing charge realizes every n.

**Theorem 1.3 (zero rank point spectrum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.zero_rank_point_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.zero_rank_point_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When rank(D)=0, original omega vanishes and the actual carrier is the existing nonzero vacuum line. The actual point spectrum consists exactly of zero.

**Theorem 1.4 (bottom fiber).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.bottom_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.bottom_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A label has bottom weight if and only if its charge minimizes q_mu and its oscillator exponent is zero. Several minimizing charges are allowed.

**Theorem 1.5 (conformal mode grade).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.conformal_mode_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.conformal_mode_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Virasoro mode L_m maps the actual rational energy-e grade to the energy-(e-m) grade for all integer m.

**Theorem 1.6 (positive modes kill bottom).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.positive_modes_kill_bottom`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.positive_modes_kill_bottom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive actual conformal mode kills EVERY vector in the full bottom space. This does not assert Virasoro generation from that space.

**Theorem 1.7 (zero rank minimum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.zero_rank_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.zero_rank_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed rational minimum h equals zero in rank zero, by the existing collapse of all actual labels.

**Definition 1.8 (halfShiftLattice).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.halfShiftLattice`

*Formalization.* `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.halfShiftLattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rank-one even integral lattice has Gram matrix [2].

**Theorem 1.9 (half shift two minima).**

Lean statement: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.half_shift_two_minima`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.half_shift_two_minima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Gram [2], mu=1/2 satisfies exact duality with beta=1. The GLOBAL bottom is 1/4 and two distinct integral charges, zero and minus one, attain it.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.bottom_fiber`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.conformal_mode_grade`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.halfShiftLattice`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.half_shift_two_minima`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.point_spectrum_subset`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.positive_modes_kill_bottom`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.positive_rank_point_spectrum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.zero_rank_minimum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeDualCosetSpectrum.zero_rank_point_spectrum`
- Dependency: [D5/S3/VertexAlgebra/LatticeDualCosetGrading](LatticeDualCosetGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeDualCosetVirasoroLaw](LatticeDualCosetVirasoroLaw.md)
