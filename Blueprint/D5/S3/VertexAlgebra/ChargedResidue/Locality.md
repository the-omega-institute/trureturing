# Complete Charged Residue Tail

## Abstract

Independent tails of the complete charged physical residue.

**Theorem 1.1 (The complete row vanishes at every padded locality cutoff).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/Locality.chargedPhysicalResidueRow_tail`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/Locality.chargedPhysicalResidueRow_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Let D be arbitrary lattice data with unit Gram determinant, sigma and tau arbitrary charges, epsilon and eta either projected sign, and gamma, delta, r, n arbitrary signed integer lifts and indices. For every natural K at least natAbs(bilinear D sigma tau), put L=((K:Int)-r).toNat. For every natural l with L <= l and every x:ActualTensor D hu, the complete forward-minus-reverse physical residue row is zero. The boundary l=L, K=0 and L=0 are included.

Both projections are expanded into their reflected charge components. All four charged commutators have the same locality order, which is padded to K by the actual difference operator. Nonnegative residue extraction then annihilates the complete row. This argument uses neither the collision-row transform nor the source comparison and asserts no separate vanishing of an ordered branch.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/Locality.chargedPhysicalResidueRow_tail`
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/Residue](../GroundRightCurrentTransport/Residue.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedResidue](../LatticeHalfFockChargedResidue.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality](../LatticeHalfFockPhysicalWordLocality.md)
