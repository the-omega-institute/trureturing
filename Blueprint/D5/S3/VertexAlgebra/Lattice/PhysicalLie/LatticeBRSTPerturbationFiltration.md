# Fixed energy and signed filtration for the original lattice BRST charge

## Abstract

Fixed energy and signed filtration for the original lattice BRST charge

The carrier is the actual State D, the all-charge lattice matter carrier tensored with the original countable bc occupation Fock space. D and its rank, null frame F, transverse dimension t and basis B retain their original quantifiers. H has both inverse-Gram hypotheses wherever the source requires them. Charge beta is integral; level and filtration lower are arbitrary integers. Q is the original LatticeBRST.totalCharge D H, and all basis statements use the original actualBasis F B.

The signed degree bounds retain both exceptional ghost zero-mode occupations. The sector restrictions concern the original BRST charge and do not assert a physical no-ghost theorem.

**Definition 1.1 (Charge ground energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.groundEnergy`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.groundEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every lattice D and integral charge beta, groundEnergy beta is bilinear D beta beta, cast to C, divided by 2.

**Definition 1.2 (Actual total zero mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and matrix H of size Fin D.rank, totalL0 H is the original matter mode at 0 plus the original ghost Virasoro mode at 0, on the full State D.

**Definition 1.3 (Oscillator frequency level).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.oscillatorLevel`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.oscillatorLevel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every transverse dimension t and exponent vector m, oscillatorLevel m is Finsupp.weight frequencyWeight m.

**Definition 1.4 (Integer level of every raw occupation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.indexLevel`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.indexLevel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every StateIndex D t, indexLevel is oscillatorLevel plus BcGhostRelativeEnergy.relativeEnergy of the raw ghost occupation. No occupation is discarded.

**Theorem 1.5 (Full signed degree window).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.degree_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.degree_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, t and raw index i, -indexLevel i <= degree i and degree i <= indexLevel i + 1. The original degree is exponentDegree plus ghost charge minus 1. Both occupations {1} and {1,3} remain.

**Theorem 1.6 (Energy of the actual basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, null frame F, transverse basis B, H satisfying both H * gramComplex D = 1 and gramComplex D * H = 1, and every i, totalL0 H applied to actualBasis F B i equals (groundEnergy i.1.1 + (indexLevel i : C) - 1) times that same basis vector.

**Theorem 1.7 (Diagonal form on the actual basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary D, F, B and H with both inverse-Gram identities, totalL0 H is diagonal on actualBasis F B with eigenvalue groundEnergy i.1.1 + (indexLevel i : C) - 1.

**Definition 1.8 (Literal fixed charge and total energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.fixedSector`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.fixedSector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, H, integral charge beta and integer level, fixedSector H beta level is the submodule of the full State D defined by chargeProject beta v = v and totalL0 H v = (groundEnergy beta + (level : C) - 1) times v. There is no global energy cutoff.

**Theorem 1.9 (Exact coefficient characterization of the sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_fixedSector_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_fixedSector_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary F and B and both inverse-Gram identities for H, v belongs to fixedSector H beta level if and only if every nonzero actualBasis coefficient has charge beta and indexLevel equal to level. All integer levels remain quantified.

**Theorem 1.10 (Each basis vector lies in its own sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.basis_mem_fixedSector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.basis_mem_fixedSector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every raw index i and both inverse-Gram identities, actualBasis F B i belongs to fixedSector H i.1.1 (indexLevel i).

**Definition 1.11 (Original signed filtration).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.signedFiltration`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.signedFiltration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary beta and integers level and lower, signedFiltration F B beta level lower is the C-span of the actual basis vectors with charge beta, indexLevel equal to level and lower <= degree. It is a submodule of the original State D.

**Theorem 1.12 (Exact coefficient characterization of the filtration).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_signedFiltration_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_signedFiltration_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every beta, integer level and lower, and v in the full State D, filtration membership is equivalent to every nonzero actualBasis coefficient satisfying exactly charge beta, indexLevel equal to level and lower <= degree.

**Theorem 1.13 (Lower endpoint for every sector vector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.sector_mem_filtration`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.sector_mem_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With both inverse-Gram identities, every v in fixedSector H beta level belongs to signedFiltration F B beta level (-level), for every integral beta and integer level.

**Theorem 1.14 (Exhaustion above the actual upper endpoint).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.filtration_exhausted`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.filtration_exhausted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every beta and integers level and lower with level + 1 < lower, signedFiltration F B beta level lower is bottom. No positivity or critical-rank assumption is added.

**Theorem 1.15 (Original Q commutes with total energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_Q`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rank and H satisfying both inverse-Gram identities, totalL0 H commutes with the original LatticeBRST.totalCharge D H. This is the existing covariance at mode zero, where its anomaly vanishes in every rank.

**Theorem 1.16 (Original Q preserves the literal sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.Q_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.Q_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F, B, H satisfying both inverse-Gram identities, integral beta, integer level and v in fixedSector H beta level, the original LatticeBRST.totalCharge D H v remains in that same sector.

**Theorem 1.17 (The leading differential commutes with total energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_d0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every null frame F, H satisfying both inverse-Gram identities and integral beta, totalL0 H commutes with the existing d0 F beta. The paired current and ghost mode indices range over all integers.

**Theorem 1.18 (The existing homotopy commutes with total energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_h`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F, B, H satisfying both inverse-Gram identities and integral beta, totalL0 H commutes with the original h F B beta.

**Theorem 1.19 (The leading differential preserves the literal sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.d0_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.d0_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F, B, H satisfying both inverse-Gram identities, beta, integer level and sector vector v, d0 F beta v remains in fixedSector H beta level.

**Theorem 1.20 (The homotopy preserves the literal sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.h_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.h_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F, B, H satisfying both inverse-Gram identities, beta, integer level and sector vector v, h F B beta v remains in fixedSector H beta level.

**Theorem 1.21 (The actual zero-count projector preserves the sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.P0_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.P0_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F, B, H satisfying both inverse-Gram identities, beta, integer level and sector vector v, P0 F B v remains in fixedSector H beta level. Both exceptional ghost zero-mode occupations remain available.

Finite homological transfer uses the sector restrictions and filtration bounds. Its critical-rank hypothesis belongs to that construction; the fixed-energy filtration itself retains arbitrary rank.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.P0_preserves`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.Q_preserves`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.basis_mem_fixedSector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.d0_preserves`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.degree_bounds`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.filtration_exhausted`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.fixedSector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.groundEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.h_preserves`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.indexLevel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_fixedSector_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_signedFiltration_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.oscillatorLevel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.sector_mem_filtration`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.signedFiltration`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_Q`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_basis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_d0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_h`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy](../../../Quantum/Fermionic/BcGhostRelativeEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising](../LatticeBRSTFullOriginalRaising.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare](../LatticeBRSTSquare.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](../../LatticeSugawaraConformal.md)
