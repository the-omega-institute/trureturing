# Four-field FullIO reassociation readout

## Abstract

Finite-target four-field outer collision readout and the explicit two-path
FullIO reassociation equality.

**Theorem 1.1 (actual_four_field_fullIO_middle_readout).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout.actual_four_field_fullIO_middle_readout`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout.actual_four_field_fullIO_middle_readout` (`✓ std3`). ∎

**Theorem 1.2 (fourField_reassociation_path_eq).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout.fourField_reassociation_path_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout.fourField_reassociation_path_eq` (`✓ std3`). ∎

## Commentary

The readout keeps the original four-field locality order, truncation telescope,
signed product identities and middle-fiber support. For each fixed pair of
inner modes, supported FullIO transport gives finite clearing data and the
outer cleared iterate is the finite contraction of the same original middle
numerator, including negative target coordinates.

For four charges, `fourFieldShortPath` applies
`fullChannel α β (γ + δ)` and then `fullChannel (α + β) γ δ`.
`fourFieldAlternatePath` first transports `β + (γ + δ)` to `(β + γ) + δ`,
applies `fullChannel α (β + γ) δ`, and transports the left charge from
`α + (β + γ)` to `(α + β) + γ`. The equality is proved after applying the
actual target `fullUniversal` inverse; the incoming maps are the same linear
map and the charge-law proofs are transported explicitly. The readout theorem
is invoked in `actual_four_field_fullIO_reassociation` before the path result.

This is a coefficient-level FullIO reassociation equality. It asserts no full
pentagon, braiding, analytic sewing, string-theory realization or AdS/CFT
claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout.actual_four_field_fullIO_reassociation`
- Readout: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout.actual_four_field_fullIO_middle_readout`
- Channel transport: `D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport.fullChannel`
