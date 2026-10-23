# SourceToQ

## Abstract

Actual charged residue comparison.

**Theorem 1.1 (The original source equals the actual Q field).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.chargedGroundSource_to_Q`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.chargedGroundSource_to_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original matching charged ground pair and signed lifts, the physical slice of the original source iterate equals the existing Q field on the actual tensor carrier, at every locality bound K at least the absolute pairing. Equality is proved coefficientwise from the actual inverse and public all-N source composition.

**Theorem 1.2 (The matching-sector ground-pair supplier).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.charged_sector_ground_pair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.charged_sector_ground_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The complete source-to-Q equality, the independent source tail and shifted actual locality recover the full three-supported original-source coefficient law. This constructs SectorGroundPair for every lattice with unit determinant and every pair of projected charges, signs and matching signed lifts. Zero charges, rank zero, degenerate sectors and arbitrary oscillator inputs remain in scope. This supplies the ground-pair hypothesis of the existing sector propagation theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.chargedGroundSource_to_Q`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/SourceToQ.charged_sector_ground_pair`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/Forward](Forward.md)
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/SectorPropagation](../GroundRightCurrentTransport/SectorPropagation.md)
