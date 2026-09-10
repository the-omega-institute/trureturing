# InvariantTube

## Abstract

Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.

**Theorem 1.1 (row at centers).**

Lean statement: `D5/S3/HardCoreHolomorphic/InvariantTube.row_at_centers`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/InvariantTube.row_at_centers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real centers are mapped to the correct real parent center, for every pruning set including the leaf and activity zero.

**Theorem 1.2 (jacobian tube sum).**

Lean statement: `D5/S3/HardCoreHolomorphic/InvariantTube.jacobian_tube_sum`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/InvariantTube.jacobian_tube_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual complex Jacobian retains a strict margin on the entire tube. The real-row value at the chosen real anchor suffices for this local comparison.

**Theorem 1.3 (row tube stability).**

Lean statement: `D5/S3/HardCoreHolomorphic/InvariantTube.row_tube_stability`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/InvariantTube.row_tube_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniform stability is derived by integrating the true differential along straight message/activity segments. There is no supplied complex Lipschitz or complex-invariance premise.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/InvariantTube.jacobian_tube_sum`
- Truth anchor: `D5/S3/HardCoreHolomorphic/InvariantTube.row_at_centers`
- Truth anchor: `D5/S3/HardCoreHolomorphic/InvariantTube.row_tube_stability`
- Dependency: [D5/S3/HardCoreHolomorphic/RowTubeBounds](RowTubeBounds.md)
