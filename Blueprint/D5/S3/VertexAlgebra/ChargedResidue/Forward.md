# Forward

## Abstract

Actual charged residue comparison.

**Theorem 1.1 (The complete arbitrary-input forward formula).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalResidueRow_forward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalResidueRow_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all original lattices, charges, projected signs, both matching integer lifts, residue indices and actual inputs, R_l is the sum for k<L-l of choose(gamma/2,k) times C_(l+k), where L=(K-r).toNat and K is any natural bound on the absolute pairing. The two whole ordered sums are normalized together before applying the scalar residue substitution and four reflected kernels. Finite-support additivity extends the tensor calculation to arbitrary actual inputs. The independently proved unweighted tail handles every l>=L, including the zero cutoff.

**Theorem 1.2 (The actual finite inverse and all-N source composition).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalSourceRow_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalSourceRow_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The finite Vandermonde inverse is instantiated with the proved full forward law and independent collision tail. The public all-N source-to-collision theorem then identifies the original source row at zero with the sum for l<L of choose(-gamma/2,l) times the complete residue row. This identity includes L=0 and is used to identify the actual Q field.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalResidueRow_forward`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalSourceRow_inverse`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/Reflections](Reflections.md)
