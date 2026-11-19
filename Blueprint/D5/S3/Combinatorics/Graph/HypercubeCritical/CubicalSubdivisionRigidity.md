# Cubical rigidity of the fifteen-vertex subdivision

## Abstract

Every induced cubical once-subdivision of K3,3 has a translated six-coordinate grid normal form.

This is a geometric step toward Problem 2 of Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 (https://arxiv.org/html/2610.09483v1#Thmproblem2). The argument below is a derived coordinate-cut classification; no literature priority is asserted. The original determination of f₂(Q₉) remains open. This theorem supplies neither a signing classification nor an obstruction for whole balanced supports.

**Definition 1.1 (gridHigh).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridHigh`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridHigh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let X be any Boolean cube vertex and let d index coordinates by pairs (s,i), where s is Boolean and i belongs to Fin 3. The branch point indexed by h is X with coordinates d(false,0) and d(h) toggled in sequence. The point h=(false,0) equals X because the two toggles cancel.

**Definition 1.2 (gridMiddle).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridMiddle`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridMiddle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For i,j in Fin 3, toggle coordinate d(true,j) of the branch gridHigh X d (false,i). With a=d(false,0), c₀=d(false,1), c₁=d(false,2) and bⱼ=d(true,j), the three middles in row zero are X toggled at bⱼ. The other six toggle a, the corresponding c-coordinate, and bⱼ.

**Definition 1.3 (gridSupport).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridSupport`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support is the union of the image of the six branch indices and the image of the nine middle indices. When d is injective these are the fifteen distinct grid points, including X and no additional vertices.

**Theorem 1.4 (cubical_subdivision_normal_form).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.cubical_subdivision_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.cubical_subdivision_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every dimension n and finite support C in the actual Boolean n-cube, assume IsK33Subdivision of the graph induced on C. Then there are a root X and an injective coordinate map d from Bool × Fin 3 to Fin n such that C equals gridSupport X d. Every coordinate outside the range of d equals its value at X at every vertex of C. No coordinate labels, six-dimensional face, signing, or connectedness hypothesis is supplied.

The incidence description supplies the two triples Aᵢ,Bⱼ and the nine unique middles Mᵢⱼ, and covers every actual vertex. For any fixed cube coordinate, two crossing edges cannot meet, since the same coordinate flip gives a unique neighbor. Crossing edges separated by one edge would force the opposite edge of a square; the exact two-neighbor table excludes that edge. Thus a crossing at Aᵢ forces all other B branch bits in that row to equal the bit at Aᵢ; the dual statement holds at Bⱼ. Classifying the six branch bits under these restrictions leaves constants, the six star cuts, and nine mixed cuts, up to complement. The middle bits are forced by the same restrictions.

The three edges Bⱼ--Mᵢⱼ form the block associated with Aᵢ; the dual three-edge blocks belong to the B branches. A mixed cut uses two edges of one block. A coordinate covering the third edge must use at least one of those two, contradicting uniqueness of the direction of an actual cube edge. Hence mixed cuts are absent. Each block has its own star coordinate, occurring exactly once. The resulting six directions are distinct. Reading the forced vertex bits relative to A₀ gives exactly the displayed grid; constant coordinate cuts give the fixed unused coordinates.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.cubical_subdivision_normal_form`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridHigh`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridMiddle`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity.gridSupport`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure](FifteenSliceStructure.md)
