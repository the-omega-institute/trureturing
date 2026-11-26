# Binary adjacency determines axial completions

## Abstract

A binary adjacency equation determines axial completions of the weight-32 residual.

**Theorem 1.1 (Axial completion is equivalent to the binary neighbor equations).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.binary_completion_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.binary_completion_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each bit chooses the layer of an odd singleton. In each even row their unsigned sum must equal the indicator of the even residual modulo two.

After switching the odd word by these bits, the same row condition is a congruence modulo four for its signed image. The transverse row bound restricts those image values to zero or four in absolute value outside the even singleton support, and to two on that support. The squared Huang operator supplies the complementary layer equations.

**Theorem 1.2 (Every dimer site has even parity and four odd singleton neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.binary_dimer_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.binary_dimer_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a solution of the binary equations with singleton energies 16 and 32, binary_dimer_count shows that twelve rows have absolute value four. Its proof uses the squared norm 256 and subtracts the contribution 64 from the even singletons. The geometry theorem gives even parity, exclusion from the singleton support, and four odd neighbors at every such row.

This describes the weight-32 residual in one 72-vertex case of Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Theorem 1.3 (The raw signed layers induce a cubic switched subgraph on 72 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.completion_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.completion_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied directions enumerate the actual neighbors in the induced graph. The transverse signs and axial equality give the switching identity on each occupied edge. The two disjoint layer images have total cardinality 72.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.binary_completion_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.binary_dimer_geometry`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion.completion_graph`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction](Q9PairedGeometricObstruction.md)
