# Fixed energy and signed filtration for the original lattice BRST charge

## Abstract

Fixed energy and signed filtration for the original lattice BRST charge

The carrier is the actual State D, the all-charge lattice matter carrier tensored with the original countable bc occupation Fock space. D and its rank, null frame F, transverse dimension t and basis B retain their original quantifiers. H has both inverse-Gram hypotheses wherever the source requires them. Charge beta is integral; level and filtration lower are arbitrary integers. Q is the original LatticeBRST.totalCharge D H, and all basis statements use the original actualBasis F B.

This publication proves uniform finite termination of the actual normalized perturbation h(Q-d0) on each literal fixed charge and total-energy sector, with power 2 * level.toNat + 2 for every integer level. The original signed window is -level <= degree <= level + 1, retaining both exceptional ghost occupations {1} and {1,3}. The final finite-HPL wrapper and unused P0 restriction remain complete saved future source; no compilation of that residual is claimed. This is an algebraic termination result and does not assert a physical no-ghost theorem.

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

**Theorem 1.10 (Full signed degree window).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.degree_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.degree_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original StateIndex D t, -indexLevel i <= degree i and degree i <= indexLevel i + 1. The proof uses the frequency-weight exponent bound and the ghost charge/energy split, including sites 1 and 3.

**Theorem 1.11 (Every original ket lies in its literal sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.basis_mem_fixedSector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.basis_mem_fixedSector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary D, F, t, B and H with both inverse-Gram identities, every actualBasis F B i belongs to fixedSector H i.1.1 (indexLevel i). This is used in the actual normalized perturbation basis step.

**Theorem 1.12 (Signed filtration in actual coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_signedFiltration_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.mem_signedFiltration_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary beta, integer level and integer lower, v belongs to signedFiltration F B beta level lower exactly when every nonzero actualBasis coefficient has charge beta, indexLevel equal to level, and degree at least lower.

**Theorem 1.13 (Initial lower degree bound).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.sector_mem_filtration`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.sector_mem_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For both inverse-Gram identities and every integer level, each vector in fixedSector H beta level belongs to signedFiltration F B beta level (-level). This is the base of the termination iteration.

**Theorem 1.14 (Upper endpoint exhausts the filtration).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.filtration_exhausted`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.filtration_exhausted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any integer level and lower with level + 1 < lower, signedFiltration F B beta level lower is the zero submodule. The upper signed degree bound proves this on the span generators.

**Theorem 1.15 (Original Q preserves total energy in every rank).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_Q`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary rank and both inverse-Gram identities, totalL0 H commutes with the original LatticeBRST.totalCharge D H. This uses the existing zero-mode covariance, whose anomaly is zero at mode zero.

**Theorem 1.16 (Original Q preserves the literal sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.Q_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.Q_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary integral beta, integer level and v in the literal fixedSector, the original Q v lies in the same sector. The charge and energy conditions are both preserved.

**Theorem 1.17 (Leading differential preserves total energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_d0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both inverse-Gram identities, totalL0 H commutes with the actual d0 F beta, using the locally finite quartet family and the original matter/ghost Ward identities.

**Theorem 1.18 (Actual quartet homotopy preserves total energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_h`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.totalL0_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both inverse-Gram identities, totalL0 H commutes with h F B beta = R F beta * invM F B. Both actual original factors are used.

**Theorem 1.19 (Leading differential preserves the literal sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.d0_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.d0_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original D, F, B and both inverse-Gram identities, d0 F beta maps fixedSector H beta level into itself for every integer level.

**Theorem 1.20 (Actual homotopy preserves the literal sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.h_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.h_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary original parameters and every integer level, h F B beta maps fixedSector H beta level into itself. This is consumed by the actual normalized perturbation step.

**Definition 1.21 (Actual normalized original-Q perturbation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.normalizedPerturbation`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.normalizedPerturbation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the original LatticeBRSTFiniteTransfer namespace, normalizedPerturbation F B H beta is exactly h F B beta * (LatticeBRST.totalCharge D H - d0 F beta), acting on the full original State D.

**Theorem 1.22 (Uniform original-Q finite termination).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.actual_normalized_perturbation_termination`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.actual_normalized_perturbation_termination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original D, null frame F, transverse t and B, H satisfying both inverse-Gram identities, integral beta, every integer level and v with chargeProject beta v = v and totalL0 H v = (groundEnergy beta + (level : C) - 1) times v, the 2 * level.toNat + 2 power of h F B beta * (LatticeBRST.totalCharge D H - d0 F beta) kills v. No rank-26 hypothesis, nonzero-charge condition, relative-kernel condition or energy cutoff is added. The proof constructs the all-k invariant A^k v in signedFiltration at -level + k from the actual raising and energy-preservation chain, then uses exhaustion; negative levels are included by the same arithmetic. The public qualified name remains in LatticeBRSTFiniteTransfer.

The coefficient, signed-window and operator-preservation statements are consumed proof helpers. The substantive candidate is the uniform iteration invariant and termination on all literal fixed-energy sectors; the frozen full-original raising result supplies one step and the existing relative-shell theorem does not cover this carrier sector. This proof-shape assessment requires exact-head semantic review and is not established by kernel or Frozen checks. Escape audits remain unfinished in issue 30101 except to the extent current binding evidence validates the retained degree_bounds registration.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.Q_preserves`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.actual_normalized_perturbation_termination`
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
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration.normalizedPerturbation`
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
