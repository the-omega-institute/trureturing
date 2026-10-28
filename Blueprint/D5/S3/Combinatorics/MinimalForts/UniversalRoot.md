# Minimal forts and a universal root

## Abstract

Minimal forts and a universal root.

**Definition 1.1 (Inclusion-minimal fort).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.MinimalFort`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/UniversalRoot.MinimalFort` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

A set is a nonempty fort in the existing generic graph predicate, and every subset that is a fort contains the entire set. The empty subset is among the quantified subsets but is not a fort.

**Definition 1.2 (All minimal forts).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalForts`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalForts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The finite family ranges over every finite vertex subset and retains exactly those satisfying inclusion minimality. There is no orbit quotient or chosen subclass.

**Definition 1.3 (The universal-root graph).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.cone`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/UniversalRoot.cone` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The vertex type is Option V. None is the added root. It is adjacent to every Some v; edges between Some v and Some w are exactly the base graph edges. The root has no loop.

**Definition 1.4 (Root-free vertex subsets).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.lift`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/UniversalRoot.lift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The injective map Some embeds a base subset without the root.

**Definition 1.5 (Root-containing subsets).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.rootSet`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/UniversalRoot.rootSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The subset consists of the universal root and exactly the embedded vertices of the base subset.

**Definition 1.6 (Recovering base vertices).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.baseSet`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/UniversalRoot.baseSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The recovered base subset consists exactly of vertices v whose Some v belongs to the given cone subset.

**Theorem 1.7 (Root-free forthood).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.isFort_lift_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/UniversalRoot.isFort_lift_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every finite simple base graph and every base subset, the embedded subset is a fort exactly when it is a base fort and its cardinality differs from one. The extra condition is imposed by the unselected universal root.

**Theorem 1.8 (Root-containing forthood).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.isFort_rootSet_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/UniversalRoot.isFort_rootSet_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every finite simple base graph, adjoining the selected root gives a fort exactly when the base subset is closed dominating. Each unselected base vertex already has the selected root as one neighbor and needs a selected base neighbor.

**Theorem 1.9 (No singleton fort without isolated vertices).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.fort_card_ne_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/UniversalRoot.fort_card_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

If every base vertex has a neighbor, a base fort cannot have cardinality one. A neighbor of the sole selected vertex would otherwise have exactly one selected neighbor.

**Theorem 1.10 (Connectivity of the actual graph).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.cone_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/UniversalRoot.cone_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For any finite base graph, including an empty or disconnected one, the cone is connected: the root reaches itself and is adjacent to every other vertex.

**Theorem 1.11 (All root-free minimal forts).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalFort_lift_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalFort_lift_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

If the finite base graph has no isolated vertices, embedding a subset gives a minimal fort exactly when that subset is a minimal fort of the base. Every cone subset without the root is recovered from its base vertices, so both minimality directions quantify over every subset.

**Theorem 1.12 (All root-containing minimal forts).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalFort_rootSet_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalFort_rootSet_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every finite base graph without isolated vertices and every base subset S, the subset consisting of the root and S is a minimal fort exactly when S is inclusion-minimal closed dominating and no subset of S is a nonempty base fort. Proper subsets retaining the root test minimal domination; subsets losing the root test the exclusion of base forts.

**Definition 1.13 (All rooted minimal-fort choices).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.rootedChoices`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/UniversalRoot.rootedChoices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For any finite decidable simple graph, this family filters every base vertex subset S by whether the universal root together with S is an actual inclusion-minimal nonempty fort of the cone. No dominating-set formula is substituted for the fort predicate.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.MinimalFort`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.baseSet`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.cone`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.cone_connected`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.fort_card_ne_one`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.isFort_lift_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.isFort_rootSet_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.lift`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalFort_lift_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalFort_rootSet_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.minimalForts`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.rootSet`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/UniversalRoot.rootedChoices`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite](../GeneralizedPetersen/ZeroForcingThreeFinite.md)
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination](../Graph/Domination/TrapezohedralMinimalDomination.md)
