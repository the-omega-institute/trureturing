# The paired syndrome forces signed squared energy at least 48

## Abstract

The paired syndrome forces signed squared energy at least 48.

**Theorem 1.1 (The paired syndrome forces signed squared energy at least 48).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction.paired_energy_ge_48_native`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction.paired_energy_ge_48_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the fixed little-endian Q8 chart. The word vanishes on even vertices, its odd coefficients occur exactly on the paired syndrome, and its signed adjacency is divisible by four at every vertex.

Put unit signs on the sixteen syndrome sites. The two-neighbor structure and Huang's squared operator identity give exactly 32 nonzero rows. Each requires a correction. An exterior correction reaches at most four rows and costs at least four units of energy. An interior correction reaches at most eight rows and costs at least eight. Counting the rows gives the bound.

**Theorem 1.2 (The paired syndrome excludes the order-72 signed fold).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction.no_paired_fold_at_order_72`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction.no_paired_fold_at_order_72` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume both signed fold equations, disjoint even dimer and even singleton words, dimer squared norm twelve, and combined singleton squared norm forty-eight. The fold implies even singleton squared norm sixteen.

If the signed residual is supported on the odd half and its odd coefficients occur at exactly the fixed paired syndrome, the energy bound instead forces even singleton squared norm at least twenty-four. This is a conditional obstruction for the study of Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction.no_paired_fold_at_order_72`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction.paired_energy_ge_48_native`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold](../ComponentBoundary/Q9SignedAxialFold.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedWeightSixteenSyndrome](Q9PairedWeightSixteenSyndrome.md)
