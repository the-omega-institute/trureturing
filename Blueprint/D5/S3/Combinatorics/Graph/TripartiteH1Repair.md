# Tripartite degree-one cochain repair

## Abstract

Complete-tripartite H1 exactness, antipodal minimum representatives, and exact degree-one repair coefficients on the octahedron.

**Definition 1.1 (Three actual edge families).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Edge`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge cochain has independent AB, AC, and BC values on the corresponding Cartesian products.

**Definition 1.2 (Vertex potentials).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Potential`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A potential assigns one F2 value to each vertex in each of the three parts.

**Definition 1.3 (Vertex coboundary).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.d0`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.d0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each edge receives the sum of its two endpoint potentials.

**Definition 1.4 (Triangle defect).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.d1`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.d1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect of an actual ABC triangle is the sum of its three edge values.

**Theorem 1.5 (Complete-tripartite degree-one exactness).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.ker_d1_eq_im_d0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TripartiteH1Repair.ker_d1_eq_im_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each vertex cancels twice in the triangle defect of a coboundary. For arbitrary nonempty parts, vanishing defects are equivalent to one global vertex potential. The reverse proof reconstructs the potential from anchored AB and AC rows and uses triangle equations on all three families.

**Definition 1.6 (Edge support weight).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.weight`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On three Bool parts, the weight counts all twelve actual edges, grouped by family.

**Definition 1.7 (Triangle defect count).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.defects`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.defects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count ranges over the eight actual ABC triangles.

**Definition 1.8 (Three-edge witness).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.witness`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support is AB(false,true), AC(false,false), and BC(false,false).

**Definition 1.9 (Dual cube vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Cube`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Cube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eight triangles are the vertices of the dual three-dimensional cube.

**Definition 1.10 (Antipodal triangles).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.antipode`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.antipode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All three Bool coordinates are complemented.

**Definition 1.11 (Coordinate dual path).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.cubePath`

*Formalization.* `D5/S3/Combinatorics/Graph/TripartiteH1Repair.cubePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The path changes the A, B, then C coordinate, omitting stationary steps. Its primal edge cochain has boundary equal to the two endpoints.

**Theorem 1.12 (Minimum representative of every antipodal defect fiber).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.sharp_three_edge_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TripartiteH1Repair.sharp_three_edge_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every cochain with an arbitrary antipodal defect pair, three coordinate cuts force every vertex repair to retain at least three edges. Exactness constructs a potential reaching the displayed coordinate path. The same public statement unconditionally gives the named witness's literal AB(false,true), AC(false,false), and BC(false,false) support, exactly the defects (false,true,true) and (true,false,false), weight three, defect count two, and a weight-three lower bound for every vertex repair.

**Theorem 1.13 (Exact octahedral degree-one repair coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.universal_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TripartiteH1Repair.universal_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dominic Dotterrer, Matthew Kahle (2012). *Coboundary expanders*. DOI: [10.1142/S1793525312500197](https://doi.org/10.1142/S1793525312500197). URL: <https://arxiv.org/abs/1012.5316v2>.

*Commentary.*

For any natural p and q, a universal repair with q times edge weight at most p times defect count exists exactly when three times q is at most twice p. This includes the global twice-weight versus three-defects bound. The upper estimate is prior literature, Dotterrer--Kahle Proposition 5.5 at n=3, k=1 in support-count norms. Its structural proof here pairs the even defect vertices by dual cube paths of at most three edges, then uses exactness. The published upper estimate proves sufficiency, while the antipodal cut barrier proves necessity and determines the exact coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Cube`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.Potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.antipode`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.cubePath`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.d0`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.d1`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.defects`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.ker_d1_eq_im_d0`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.sharp_three_edge_witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.universal_repair`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/TripartiteH1Repair.witness`
