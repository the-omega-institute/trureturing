# Original lattice bc-BRST charge and energy support

## Abstract

The original lattice bc-BRST state decomposes by charge and energy; for a neutral zero-energy target, full Q-image membership reduces to a preimage in the same sector.

The declarations in this unit use the original LatticeData carrier, with arbitrary natural rank, an integral symmetric Gram matrix and even diagonal. The state space is the actual complex tensor product of the lattice oscillator carrier with the algebraic bc Fock space. A basis label is a lattice charge/exponent label together with a finite ghost subset; no positivity, cutoff, finite charge window or nonisotropic restriction is introduced here.

The Support namespace isolates charge-zero states and proves the exact ghost-energy enumeration needed at the zero-energy boundary. The Image namespace uses the full tensor basis to define simultaneous charge and total-energy projections. Under H*gramComplex D=1 and gramComplex D*H=1, its coefficient-blocking results show that the original Q preserves both labels. For a target already neutral and in ker(M D H 0 + G D 0), a full State preimage can therefore be projected to that same sector without replacing Q by a different differential. This does not identify the entire range of Q with the restricted range.

The Energy namespace supplies the all-energy contracting operator. P0 is the total-energy-zero projection, EInv is the inverse energy weight away from zero, and h=(B D 0).comp(EInv D) applies EInv first and then the original B0 action. The homotopy identity and cycle reduction require both Gram inverse equations and no rank-26 premise. They reduce every Q-cycle, at any lattice charge, to a Q-cycle in the total-energy-zero sector, while preserving the original State and Q.

**Definition 1.1 (Tensor-product basis for the actual state space).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.stateBasis`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.stateBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

stateBasis is the tensor product of the existing lattice carrier basis and the finite-subset ghost basis. It is the coordinate system used by every later charge, energy and projection theorem; it is not a finite truncation of the state space.

**Definition 1.2 (Exact neutral zero-energy labels).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.zeroLabels`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.zeroLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

zeroLabels records the complete charge-zero, total-energy-zero basis-label list: the four ground ghost subsets and the two one-oscillator families indexed by a lattice axis. This is an exact enumeration in the original infinite algebraic Fock space, not a cutoff statement.

**Theorem 1.3 (One-oscillator energy classification).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.oscillator_energy_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.oscillator_energy_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oscillator energy is one exactly for a single exponent at mode zero. Together with the ghost-energy case split, this theorem supplies the complete one-oscillator part of the neutral zero-energy label classification.

**Theorem 1.4 (Neutral total-energy zero classification).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.neutral_energy_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.neutral_energy_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a neutral lattice label and a finite ghost subset, total energy is zero exactly in the ground or one-oscillator cases recorded by zeroLabels. The statement is derived from the actual lattice and ghost grading and does not assume positivity beyond the imported model facts used in the proof.

**Theorem 1.5 (Neutral T0 kernel is the native span).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.neutral_T0_kernel_eq_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.neutral_T0_kernel_eq_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the two-sided Gram inverse hypotheses, the kernel of M D H 0 + G D 0 inside the neutral submodule is exactly the span of the basis labels in zeroLabels. This is the precise zero-energy neutral reduction used by the native basis module.

**Definition 1.6 (Charge and total-energy projection).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.jointProjection`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.jointProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Image.jointProjection is the coordinate projection onto simultaneous charge-zero and total-energy-zero labels in the full tensor basis. It is defined on the complete State space and is not a projection onto a hand-selected finite subspace.

**Theorem 1.7 (Q preserves lattice-charge blocks).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.Q_charge_coeff_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.Q_charge_coeff_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary H, a Q image coefficient at a different lattice charge vanishes; this charge-only theorem needs neither Gram inverse equation nor rank 26. The proof uses the actual finite statewise Q expansion and the existing lattice-sector action, so it preserves the original all-charge operator rather than postulating a charge-truncated complex.

**Theorem 1.8 (Joint projection commutes with Q).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.jointProjection_commutes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.jointProjection_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, the simultaneous neutral and total-energy projection commutes with the original Q, with no rank-26 premise. This supplies the image-membership bridge for a target already in the neutral T0 kernel; it does not assert equality of the entire full and restricted Q ranges.

**Theorem 1.9 (Q-image membership for a neutral zero-energy target).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.full_image_iff_restricted`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.full_image_iff_restricted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume H*gramComplex D=1 and gramComplex D*H=1, and let y be a State D already satisfying y ∈ Image.neutral D intersect ker(M D H 0 + G D 0), the same E0 used in the cohomology unit. Then y ∈ range(Q D H) if and only if there exists x : State D in that same neutral T0 kernel with Q D H x=y. The left side allows a preimage anywhere in the full State; the right side requires an E0 preimage. No rank-26 premise occurs. The theorem compares membership only for such y, not the entire range of Q with the restricted range; it does not replace Q by a coordinate differential or assert a physical no-ghost theorem.

**Definition 1.10 (Inverse away from total energy zero).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.EInv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.EInv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EInv acts by the reciprocal of the integer total energy away from zero and by zero at energy zero. It is an algebraic spectral inverse on the full basis, not an analytic inverse and not a positivity or cutoff assumption.

**Theorem 1.11 (All-energy BRST homotopy identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.homotopy_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.homotopy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With both Gram inverse equations, Q*h+h*Q equals 1-P0 on the entire original State space. The proof uses the existing Ward identity for Q and B, the exact energy-block commutation, and the spectral inverse EInv. This is the all-energy neutral reduction mechanism.

**Theorem 1.12 (Every Q-cycle reduces to zero total energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.cycle_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.cycle_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both Gram inverse equations, if x : State D satisfies Q D H x=0, then y=P0 D x is Q-closed, lies in ker(M D H 0 + G D 0), and satisfies x-y=Q D H (h D x). No rank-26 premise is needed. This reduction applies to every lattice charge in the full state space, but does not compute the remaining charged zero-energy cohomology or provide physical state selection or string completion.

Reuse and attribution: the carrier, L0, bc-Fock, BRST charge, total covariance and ghost-number operations are imported from the existing D5/S3/VertexAlgebra modules. The declarations here are repository-derived consequences of those actual definitions and proofs. No new positivity, intercept, rank-26, analytic completion or finite cutoff premise is added. The separate native cohomology unit supplies the quotient, inverse, J0/ghost grading and absolute/relative dimensions built on this support.

Boundary: this unit does not close nonzero-charge cohomology, a no-ghost theorem, the full VOA/CFT construction, physical string theory or an AdS/CFT correspondence. Those remain active open goals beyond the formal consequences recorded here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.EInv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.Q_charge_coeff_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.cycle_reduction`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.full_image_iff_restricted`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.homotopy_identity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.jointProjection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.jointProjection_commutes`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.neutral_T0_kernel_eq_span`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.neutral_energy_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.oscillator_energy_one_iff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.stateBasis`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.zeroLabels`
- Dependency: [D5/S3/VertexAlgebra/BcGhostLZeroSpectrum](BcGhostLZeroSpectrum.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstCharge](LatticeBcGhostBrstCharge.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstTotalCovariance](LatticeBcGhostBrstTotalCovariance.md)
