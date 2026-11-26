# At least eighteen rows see exactly two support sites

## Abstract

A 32-site support of the eight-cube whose row degrees are zero, two, or four has at least eighteen degree-two rows.

**Theorem 1.1 (Each support site gives a local inequality on degree-two rows).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows.degreeTwoRows_add_four_at_site`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows.degreeTwoRows_add_four_at_site` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a 32-site support with row degrees zero, two, or four, let n₂ count all degree-two rows and let a count those adjacent to a chosen support site. Then n₂ + 4a is at least 22. Translate the chosen site to zero and count pairs of weight-two support sites through their common rows in layers one and three.

**Theorem 1.2 (At least eighteen rows see exactly two support sites).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows.eighteen_le_degreeTwoRows`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows.eighteen_le_degreeTwoRows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the same support and row-degree hypotheses, sum the translated local inequality over all thirty-two sites. Each degree-two row contributes once at each of its two support neighbors.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows.degreeTwoRows_add_four_at_site`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows.eighteen_le_degreeTwoRows`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction](Q9SparseSyndromeObstruction.md)
