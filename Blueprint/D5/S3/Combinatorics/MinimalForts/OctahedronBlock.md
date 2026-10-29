# Whole parts and transversals

## Abstract

Minimal forts in complete equipartite graphs with two vertices per part.

**Definition 1.1 (A whole part).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.part`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.part` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For any natural m and any i in Fin m, part i is the two-element vertex set consisting of (i,0) and (i,1). The actual graph is Mathlib's completeEquipartiteGraph m 2 on Fin m times Fin 2, with adjacency exactly when first coordinates differ.

**Definition 1.2 (A transversal).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.Transversal`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.Transversal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For any natural m and any vertex subset S, Transversal S means that the first-coordinate projection is injective on S. It is equivalent to saying that S contains no whole two-vertex part.

**Theorem 1.3 (All minimal forts).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_minimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_minimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every natural m at least two and every actual vertex subset S, S is an inclusion-minimal nonempty fort if and only if S is one whole part, or S has cardinality three and is a transversal. A set of at least three vertices is a fort because an outside vertex has at most one nonneighbor in the set. Whole parts are forts. A transversal fort must have at least three vertices: a two-element transversal leaves a mate with exactly one selected neighbor. Minimality therefore gives exactly the stated two classes, and both classes are minimal. Empty subsets and all proper subsets are included in these arguments.

**Theorem 1.4 (All choices containing the universal root).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_rooted_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_rooted_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every natural m at least two and every base subset S, rootSet S is a minimal fort in the graph with a new universal root if and only if S has cardinality two and is a transversal. The root characterization requires minimal domination and no contained base fort. Fort-freeness excludes whole parts and forces transversality; domination needs two distinct parts, while any such pair dominates and is minimal. Thus these are all rooted choices.

**Theorem 1.5 (Unbounded exact counts).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every natural m at least two the actual graph has order 2*m, its full minimal-fort count is m + 8*choose(m,3), its full rooted-choice count is 4*choose(m,2), and every vertex has a neighbor. For arbitrary natural m and k, transversals of size k are in bijection with a k-element subset of Fin m together with a function choosing one of the two vertices in each selected part. Taking first-coordinate support recovers the selected parts, and injectivity recovers each choice. This gives choose(m,k)*2^k transversals. Whole parts are indexed injectively by Fin m and are disjoint from three-element transversals. At m=2 the counts are 2 and 4; at m=3 they are 11 and 12 on six vertices. The latter specialization supplies the octahedral blocks in the mixed graph count.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.Transversal`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_block`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_minimal_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.equipartite_rooted_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.part`
- Dependency: [D5/S3/Combinatorics/MinimalForts/UniversalRoot](UniversalRoot.md)
