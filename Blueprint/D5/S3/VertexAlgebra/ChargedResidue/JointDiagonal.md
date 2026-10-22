# Joint Native Creation Diagonal

## Abstract

The complete native residue on a common creation diagonal.

**Theorem 1.1 (The two ordered chambers have one signed creation total).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal.chargedPhysicalResidueRow_joint_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal.chargedPhysicalResidueRow_joint_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original lattice, unimodularity witness, two charges, projected signs, signed lifts and residue indices, and actual pure tensor p tensor g, both matching sector equations give the complete physical residue as one finite pairTranslation sum. The creation total for a supported exponent d is U=-2*(r+n)-gamma-delta-4+Q(sigma)+Q(tau)+d(0)+d(1). For U<0 the whole diagonal is zero. Otherwise m ranges from zero through U.

Write q=r+l and a=-2*q-gamma-2+Q(sigma)+d(0). The forward contraction contributes H(m-a-2*j), while the reversed contraction contributes H(2*q-(m-a)-2*j). Here H is the actual halfContraction coefficient extended by zero at negative indices. nativeChamberScalar combines the two sums with physicalResidueWeight(q,j) and the exact factor (-1)^q*paritySign(bilinear(sigma,tau)). The two outer ranges remain the actual, separate inner-field order bounds. Neither ordered contribution is asserted to vanish.

For each forward supported monomial, the contraction cutoff uses its own right coordinate bound; the reverse uses the first coordinate transported by swapping the two variables of pairTranslation. The finite bijections discard only terms with a negative creation index, and preserve arbitrary inhomogeneous oscillator inputs and every signed lift. The tensor factor is the actual ordered ground-action product and the original product of chargeScalar values. The scalar two-chamber change of variables evaluates this diagonal. Its combination with all four reflected collision kernels gives the physical forward law, while independent tails and the finite inverse identify the original source with the actual Q field.

**Theorem 1.2 (Whole-sum enlargement preserves both ordered supports).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal.chargedPhysicalResidueRow_joint_supported`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal.chargedPhysicalResidueRow_joint_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Each actual ordered range can be enlarged independently beyond its own intermediate field-order cutoff. The added whole tensor terms vanish before expansion into translated monomials. This permits finite coefficient convolution on a range adapted to the translated support without asserting that a monomial term vanishes at the original outer cutoff.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal.chargedPhysicalResidueRow_joint_native`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal.chargedPhysicalResidueRow_joint_supported`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/CollisionTransform](CollisionTransform.md)
