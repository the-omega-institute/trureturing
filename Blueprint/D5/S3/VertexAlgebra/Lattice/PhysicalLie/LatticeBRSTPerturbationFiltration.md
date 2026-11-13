# Fixed energy and signed filtration for the original lattice BRST charge

## Abstract

Fixed energy and signed filtration for the original lattice BRST charge

The carrier is the actual State D, the all-charge lattice matter carrier tensored with the original countable bc occupation Fock space. D and its rank, null frame F, transverse dimension t and basis B retain their original quantifiers. H has both inverse-Gram hypotheses wherever the source requires them. Charge beta is integral; level and filtration lower are arbitrary integers. Q is the original LatticeBRST.totalCharge D H, and all basis statements use the original actualBasis F B.

This publication characterizes the literal fixed charge and energy sector. The signed bounds and operator restrictions are preserved with the complete future finite-transfer source; their compilation is not claimed here. The original signed degree and both exceptional ghost occupations remain unchanged in that source. This does not assert a physical no-ghost theorem.

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

**Theorem 1.5 (Energy of the actual basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, null frame F, transverse basis B, H satisfying both H * gramComplex D = 1 and gramComplex D * H = 1, and every i, totalL0 H applied to actualBasis F B i equals (groundEnergy i.1.1 + (indexLevel i : C) - 1) times that same basis vector.

**Theorem 1.6 (Diagonal form on the actual basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary D, F, B and H with both inverse-Gram identities, totalL0 H is diagonal on actualBasis F B with eigenvalue groundEnergy i.1.1 + (indexLevel i : C) - 1.

**Definition 1.7 (Literal fixed charge and total energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.fixedSector`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.fixedSector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, H, integral charge beta and integer level, fixedSector H beta level is the submodule of the full State D defined by chargeProject beta v = v and totalL0 H v = (groundEnergy beta + (level : C) - 1) times v. There is no global energy cutoff.

**Theorem 1.8 (Exact coefficient characterization of the sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_fixedSector_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_fixedSector_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary F and B and both inverse-Gram identities for H, v belongs to fixedSector H beta level if and only if every nonzero actualBasis coefficient has charge beta and indexLevel equal to level. All integer levels remain quantified.

**Definition 1.9 (Original signed filtration).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.signedFiltration`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.signedFiltration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary beta and integers level and lower, signedFiltration F B beta level lower is the C-span of the actual basis vectors with charge beta, indexLevel equal to level and lower <= degree. It is a submodule of the original State D.

The original State D, total charge, both inverse-Gram hypotheses, arbitrary rank and all integer levels are retained. The coefficient characterization and its two consumed energy helpers are the three current public theorems. Their escape audits remain unfinished in issue 30101; the characterization has no certified escape-witness classification.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.fixedSector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.groundEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.indexLevel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_fixedSector_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.oscillatorLevel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.signedFiltration`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_basis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_diagonal`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy](../../../Quantum/Fermionic/BcGhostRelativeEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising](../LatticeBRSTFullOriginalRaising.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare](../LatticeBRSTSquare.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](../../LatticeSugawaraConformal.md)
