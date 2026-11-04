# Local output compression budgets

## Abstract

Actual Schatten compression budgets glue over complete orthogonal local output resolutions.

**Theorem 1.1 (Pinching the actual row maps).**

Lean statement: `D5/S3/Quantum/NormCompression/LocalOutputGluing.row_piece_schattenPow_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/LocalOutputGluing.row_piece_schattenPow_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite family of isometric output embeddings whose range projections sum to the identity, and every real 1 <= q <= 2, the sum of the 2q-th Schatten powers of the projected row pieces is bounded by the 2q-th Schatten power of the original arbitrary rectangular complex matrix. The proof applies the existing full PSD positive unital Jensen theorem to each actual Gram matrix, then sums the trace bounds using the complete output resolution. Empty input, output and component dimensions are included.

**Definition 1.2 (Actual column power table).**

Lean statement: `D5/S3/Quantum/NormCompression/LocalOutputGluing.columnPowerTable`

*Formalization.* `D5/S3/Quantum/NormCompression/LocalOutputGluing.columnPowerTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two row entries are the actual 2q-th Schatten powers of the two corresponding rectangular complex block maps. Applying Aq to this table recovers the repository norm compression matrix exactly.

**Theorem 1.3 (Gluing the actual compression budget).**

Lean statement: `D5/S3/Quantum/NormCompression/LocalOutputGluing.local_output_compression_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/LocalOutputGluing.local_output_compression_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 1 < q < 2, every finite column family of arbitrary rectangular complex maps, and complete finite isometric resolutions of both local outputs, the sum of the 2q-th Schatten powers of the component compression matrices is bounded by the 2q-th Schatten power of the global compression matrix. The proof uses the proved finite power cone concavity on the actual column power tables and their entrywise domination from row pinching. Local output dimensions and original column dimensions may vary and may be empty. This is the compression budget step of local orthogonal output gluing. It does not assert the remaining unrestricted common majorant optimization or the original Audenaert inequality.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/LocalOutputGluing.columnPowerTable`
- Truth anchor: `D5/S3/Quantum/NormCompression/LocalOutputGluing.local_output_compression_budget`
- Truth anchor: `D5/S3/Quantum/NormCompression/LocalOutputGluing.row_piece_schattenPow_sum_le`
- Dependency: [D5/S3/Quantum/Lieb/PositiveMapJensen](../Lieb/PositiveMapJensen.md)
- Dependency: [D5/S3/Quantum/Lieb/PowerConvexity](../Lieb/PowerConvexity.md)
- Dependency: [D5/S3/Quantum/NormCompression/FinitePowerConcavity](FinitePowerConcavity.md)
