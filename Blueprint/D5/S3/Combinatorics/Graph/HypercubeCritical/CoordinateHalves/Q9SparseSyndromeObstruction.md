# Shell capacity bounds signed lifts of sparse cube syndromes

## Abstract

Shell capacity bounds signed lifts of sparse cube syndromes.

**Theorem 1.1 (The signed lift energy is bounded by the exterior shell capacity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction.sparse_syndrome_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction.sparse_syndrome_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every row has zero or two neighbors in the odd support. Huang’s squared operator identity makes exactly twice the support cardinality of the unit-signed rows nonzero. Each such row needs a correction for divisibility by four. The shell of a corrected site inside the support reaches at most eight rows and costs at least eight units of squared energy. An exterior correction reaches at most the specified shell capacity and costs at least four.

**Theorem 1.2 (The order-72 fold forces the sparse syndrome to be empty).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction.sparse_syndrome_empty_at_order_72`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction.sparse_syndrome_empty_at_order_72` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two fold equations fix the residual squared norm at 32 when there are twelve dimers and forty-eight singleton sites. The energy bound allows at most sixteen syndrome sites. Below sixteen, the binary adjacency kernel classification leaves the empty word, one shell, and a symmetric difference of two shells. The latter two have a row with more than two syndrome neighbors. At weight sixteen, some nonzero residual site outside the syndrome must have all eight of its neighbors among the rows with two syndrome neighbors. Otherwise the exterior capacity is at most seven, which forces the weight below sixteen.

Translate that exterior site to the origin. The eight syndrome sites at distance two give a two-regular graph on the coordinate set. At least thirty-two distance-three rows each see one of those sites and need a second neighbor at distance four. This uses the entire allowance of eight more sites and all of their lower neighbors. Two distance-four sites with a common distance-five row also have a common distance-three row. The lower rows each admit just one distance-four site, so each distance-five row adjacent to a syndrome site sees exactly one. This violates the row hypothesis.

The fold is a conditional case in Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction.sparse_syndrome_empty_at_order_72`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction.sparse_syndrome_energy`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeAnalyticWeightTwelve](BinaryCubeAnalyticWeightTwelve.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction](Q9PairedGeometricObstruction.md)
