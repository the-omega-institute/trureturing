# One common phase normalization

## Abstract

Every original phase vector admits one common integer translation. This does not choose separate phases at separate points.

**Theorem 1.1 (Exhaustive common normalization).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Normalization.normalize_original_phases`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203Normalization.normalize_original_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One translation normalizes the seven base phases to domains of sizes 1, 1, 2, 2, 4, 6 and 1, and transforms every original row event with that same translation.

**Theorem 1.2 (Exact six-row homogeneous kernel).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Normalization.six_row_kernel_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203Normalization.six_row_kernel_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first six actual homogeneous congruences hold exactly at integer linear combinations of (360,0) and (228,24).

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203Normalization.normalize_original_phases`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Normalization.six_row_kernel_coordinates`
- Dependency: [D5/S3/Arith/Covering/Erdos203Rows](Erdos203Rows.md)
