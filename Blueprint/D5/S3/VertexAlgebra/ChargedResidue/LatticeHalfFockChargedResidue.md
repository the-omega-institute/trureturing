# Charged Two-Order Physical Residue

## Abstract

Charged projected-ground residue rows on the original actual half-Fock tensor carrier.

For D:LatticeData, hu:IsUnit D.G.det, signed charges sigma and tau, Boolean projected signs, signed lifts gamma, delta, r, n, and arbitrary x:ActualTensor D hu, the source and collision rows retain all four reflected charge components. The output exponent is the unreduced integer -2*(n-l)-gamma-delta-2, and the physical residue keeps both ordered branches with the public integerBinomial convention.

**Theorem 1.1 (The public all-N source comparison is composed on all four projected components).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.charged_ground_source_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.charged_ground_source_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The projected-ground expansion is performed on Carrier D. Each reflected bare source is transported by the public all-N comparison to the normalized collision coefficient on ActualTensor D hu. Ground-action multiplication supplies the single actual cocycle and the chargeScalar normalization; no private all-N endpoint or second cocycle is introduced.

**Theorem 1.2 (Concrete physical source rows equal the four reflected collision rows).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_eq_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_eq_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Every signed row index and every actual tensor input is retained. The theorem is the source side of the intended residue comparison and does not identify the physical two-order residue with that row.

**Theorem 1.3 (Projected physical slices expand into both reflected charged fields).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.projectedGround_slice_mode_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.projectedGround_slice_mode_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The expansion is pointwise on the original ActualTensor carrier and preserves the signed lift and exact physical exponent. Both reflected components remain available to the later ordered-kernel telescope.

**Theorem 1.4 (The four reflected collision rows have an independent unweighted outer tail).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalCollisionRow_tail`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalCollisionRow_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For l at or beyond ((K:Int)-r).toNat, with natAbs(bilinear sigma tau) ≤ K, every reflected source degree is negative. This includes zero charge, rank-zero data, K=0 and the boundary l=L.

**Theorem 1.5 (The left physical branch has pointwise finite support).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_left_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_left_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The corresponding right branch is recorded by chargedPhysicalResidueRow_right_finite. The finite support bounds come from the actual input order of the inner field, separately for each branch; neither branch is declared zero.

**Theorem 1.6 (Finite binomial inversion is proved with the zero-cutoff case).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.charged_finite_binomial_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.charged_finite_binomial_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The finite triangular inverse reindexes finite sums and consumes Ring.add_choose_eq. L=0 is discharged from the explicit tail rather than a positive-cutoff argument. Its charged forward-row hypothesis still has to be proved for the actual physical rows before this generic inverse can be instantiated.

The construction uses the public StateFieldResidueReconstruction integerBinomial, physicalSlice_mode, native_ordered_product and the existing actual ground-action/collision APIs. The remaining mathematical gap is the native two-order forward telescope on arbitrary actual inputs and the resulting charged-family inverse instantiation. ChargedResidue.Locality proves the independent complete-residue tail, including the zero cutoff. No full VOA, CFT, string or AdS/CFT claim is made. Classical residue and twisted-lattice background is attributed to the inherited repository sources and FLM; no literature novelty is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalCollisionRow_tail`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_left_finite`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_eq_collision`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.charged_finite_binomial_inverse`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.charged_ground_source_collision`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue.projectedGround_slice_mode_expansion`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateLocality](../LatticeAllStateLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision](../LatticeHalfFockChargedCollision.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport](../LatticeHalfFockGroundRightCurrentTransport.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling](../LatticeHalfFockPhysicalRescaling.md)
