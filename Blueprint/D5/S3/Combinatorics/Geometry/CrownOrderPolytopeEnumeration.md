# Crown composition enumeration

## Abstract

Indexed compositions support the cyclic partition count.

The parity-adjusted composition construction follows source Lemma 3.5, with an equivalence stated for all natural parameters, including empty and impossible cases. Original-block connectivity supplies a formal detail of the cycle argument in Lemma 3.2.

**Definition 1.1 (Prescribed odd parts and evenization).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.parityCompositionEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.parityCompositionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

The explicit equivalence separates an indexed composition with a prescribed number of odd parts into the set of odd positions and the positive residual composition obtained by parity adjustment. This implements the composition step of the published enumeration; support and inverse maps are part of the construction.

**Theorem 1.2 (Original blocks are connected in the cycle).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.crownPartition_originalBlock_cycleGraph_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.crownPartition_originalBlock_cycleGraph_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two, an original-vertex block of an augmented connected compatible partition that meets neither endpoint induces a connected subgraph of the cycle on 2n vertices. The alternating order relation is related to the undirected cycle before the block path is extracted.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.crownPartition_originalBlock_cycleGraph_connected`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration.parityCompositionEquiv`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP](CrownOrderPolytopeCCP.md)
