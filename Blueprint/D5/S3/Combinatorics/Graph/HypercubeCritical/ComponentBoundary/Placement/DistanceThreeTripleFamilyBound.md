# At least eighteen triples

## Abstract

A lower bound for triple families with restricted pair degrees.

**Definition 1.1 (Codegree of a face).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound.codegree`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound.codegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count the selected triples containing the face.

**Theorem 1.2 (The eighteen-triple lower bound).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound.card_ge_eighteen`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound.card_ge_eighteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a nonempty family of triples. Every occurring pair has codegree two or three, each triple contains at most one pair of codegree two, and each four-set contains at most two selected triples. The three pairs of a selected triple allow at least five extensions to other triples. Their new axes are distinct because every four-set contains at most two selected triples. In an axis link, the three neighbors of a degree-three axis are independent and each has degree at least two. Thus every link has at least six edges. At eight axes the pair-degree counts force the family size to be divisible by six. These estimates give eighteen triples in all cases.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound.card_ge_eighteen`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound.codegree`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount](MinimumContactDisplacementCount.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/TripleContactFamilyBound](TripleContactFamilyBound.md)
