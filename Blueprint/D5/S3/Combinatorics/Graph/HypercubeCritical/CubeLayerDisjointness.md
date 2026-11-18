# Cube-coordinate disjoint-neighborhood invariant

## Abstract

The actual distance-four cubic layer has pairwise disjoint neighborhoods in an induced Boolean cube graph of girth at least eight.

The external research anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2). This is a repository-derived general invariant motivated by that Q₉ research line; literature novelty is unconfirmed. It establishes neither the complete 24-vertex slice classification nor the original 258-point problem. The complementary abstract breadth-first counting argument is a separate prospective consumer and is not an input or dependency.

Let G be a finite simple graph with an injective induced embedding f into an arbitrary finite Boolean cube, and with extended girth at least eight. Use an actual bipartition L,R with the root x in L. Define Tₓ by G.edist x y = 4, G.degree y = 3, and G.edist x u = 3 for every actual neighbor u of y. Distances are extended natural numbers, so vertices in disconnected components cannot enter these finite distance layers. Property (D) says that distinct y,z in Tₓ have disjoint G-neighborhoods. There is no balance, regularity, dimension bound, fan certificate, Hamming-distance hypothesis, or assumed neighborhood disjointness.

The proof obtains length-three walks from the actual extended distance using Mathlib's exists_walk_of_edist_eq_coe. Their nonbacktracking conditions follow from distance three; the extra nonbacktracking condition for the appended edge follows from distance four. Degree three supplies exactly two further neighbors besides any chosen neighbor. The girth-based short-path uniqueness lemmas in GirthSliceCounting, applied in reverse from y, force the three first vertices to be distinct. Their use also excludes every forced crossing that would create a 4-cycle or a pair of distinct simple three-edge paths.

Every simple three-edge segment flips three distinct coordinates. Consecutive repetition contradicts vertex injectivity; repetition of the first and third directions would create a cube edge between the segment's endpoints, whose induced reflection gives a forbidden 4-cycle. Suppose a four-edge branch has different first and last directions. Its four directions are then distinct, and the set of coordinates differing between f(x) and f(y) has cardinality four. Each branch's four directions must equal that same set, by support inclusion and cardinality. The three distinct first directions and the exclusion of 4-cycle crossings force all three second directions to equal the one remaining coordinate. The first branch's third direction is then another branch's first direction, forcing a crossing that yields two different length-three paths to the same endpoint. Girth excludes it. Thus each branch's first and last directions agree.

If y,z share a neighbor w, take one actual shortest three-edge prefix from x to w and append wy or wz. The preceding fan argument forces both final edges to flip the prefix's first direction. A cube vertex has only one neighbor in a given direction, and injectivity of f gives y=z. All supporting graph, path and coordinate declarations are private and are consumed by the closed refutation result.

**Definition 1.1 (Existence of an actual failure of property (D)).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed proposition quantifies n,m, a SimpleGraph on Fin m, an injective map into Fin n → Bool preserving and reflecting adjacency, finite bipartition sets L,R, and x,y,z,w. It requires x∈L, extended girth ≥8, actual extended distances four from x to y,z, degree three for y,z, distance three for every neighbor of either, y≠z, and actual edges yw and zw. The definition has literal type Prop and contains no surrogate coordinate or path premise.

**Theorem 1.2 (Property (D) holds in every finite induced cube graph of girth at least eight).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem has literal type ¬ claim. It refutes the actual common neighbor obstruction uniformly in graph size and cube dimension. Its proof derives the fan, nonbacktracking conditions and edge directions from the graph hypotheses, using actual shortest walks and girth-based path uniqueness. No classification or counting certificate is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting](GirthSliceCounting.md)
