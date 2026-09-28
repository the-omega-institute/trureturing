# Octahedral cochain sharpness

## Abstract

Four path faces give two antipodal defects and a sharp edge-repair barrier.

The boundary of the four-dimensional cross-polytope has four opposite vertex pairs. A tetrahedron chooses one vertex from each pair. A triangle omits one pair and chooses one vertex from each remaining pair; faces and simplicial edges are unordered and have no repeated vertices.

**Definition 1.1 (Tetrahedral vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.tetraVertices`

*Formalization.* `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.tetraVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A four-bit word determines the unordered set of four vertices obtained by taking its bit from each of the four opposite pairs.

**Definition 1.2 (Triangular vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.triangleVertices`

*Formalization.* `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.triangleVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A missing coordinate and three remaining bits determine an unordered three-vertex face. Every valid unordered triangle occurs exactly once.

**Definition 1.3 (Edge coboundary).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.d1`

*Formalization.* `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.d1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value of d1(e) on a triangle is the sum in F2 of e on its three unordered two-vertex subsets.

**Definition 1.4 (Tetrahedral coboundary).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.d2`

*Formalization.* `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.d2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value of d2(F) at a tetrahedron is the sum in F2 of the values on its four incident unordered triangles.

**Definition 1.5 (Triangular support weight).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.weight`

*Formalization.* `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight of a triangle cochain counts each of the 32 valid triangles once when its value is nonzero.

**Definition 1.6 (Tetrahedral defect count).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.defects`

*Formalization.* `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.defects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect count is the number of the 16 tetrahedra on which d2(F) is nonzero.

**Definition 1.7 (The antipodal path cochain).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.path`

*Formalization.* `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cochain P equals one on the four cube edges in directions 0, 1, 2, and 3 along the path 0000 to 1000 to 1100 to 1110 to 1111, and zero on every other triangle.

**Theorem 1.8 (Four errors for two antipodal defects).**

Lean statement: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.antipodal_repair_sharpness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.antipodal_repair_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are 16 tetrahedra and 32 triangular coordinate faces. The coordinate-face map is a bijection onto all valid unordered three-vertex faces; every tetrahedron has four vertices, and its four coordinate triangles are subsets of its vertex set.

The path cochain P has weight four and defect count two. For every edge cochain e on unordered vertex pairs, the triangle cochain P+d1(e) has weight at least four. Equality is attained by e=0, so the minimum repair weight is four.

For each missing coordinate, summing tetrahedral defects on its zero side cancels all internal triangles in F2 and leaves the triangle sum in that direction. Exactly one antipodal defect lies on that side. The four disjoint direction classes therefore each contain an error. The identity d2(d1(e))=0 transfers this argument to every edge repair.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.antipodal_repair_sharpness`
- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.d1`
- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.d2`
- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.defects`
- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.path`
- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.tetraVertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.triangleVertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.weight`
