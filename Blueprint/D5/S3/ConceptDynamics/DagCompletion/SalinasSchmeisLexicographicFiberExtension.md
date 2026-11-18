# Extensions by lexicographic fibers

## Abstract

Lexicographic extensions partitioned into inherited fibers.

**Definition 1.1 (The first-coordinate fiber).**

$$\forall P \in Type u,\; \forall A \in Type v,\; \forall p \in P,\; \operatorname{lexFiber}\left(p\right) = \{x \in \operatorname{Lex}\left(\operatorname{Prod}\left(P, A\right)\right) \mid \operatorname{ofLex}\left(x\right).1 = p\}$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The carrier is Lex(Prod(P,A)), with the lexicographic partial order supplied by Mathlib. A fiber is the literal subset on which the first coordinate equals the index, with the order inherited from the product.

**Definition 1.2 (The induced base embedding).**

$$\forall P \in Type u,\; \forall A \in Type v,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{PartialOrder}\left(A\right)] \forall a \in A,\; \forall p \in P,\; \operatorname{lexBaseEmbedding}\left(a\right)\left(p\right) = \operatorname{toLex}\left((p, a)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexBaseEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Fix a point of A. The map preserves and reflects the base order since the two second coordinates are the same. Equality of the lifted first coordinates also gives injectivity.

**Definition 1.3 (The inherited fiber order).**

$$\forall P \in Type u,\; \forall A \in Type v,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{PartialOrder}\left(A\right)] \forall p \in P,\; \forall a \in A,\; (\operatorname{lexFiberOrderIso}\left(p\right)\left(a\right)).val = \operatorname{toLex}\left((p, a)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiberOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Insert the second coordinate at the fixed first coordinate. The inverse reads the second coordinate, and the strict first-coordinate comparison is impossible within the fiber. The resulting comparison is exactly the comparison in A.

**Theorem 1.4 (The literal fiber partition).**

$$\forall P \in Type u,\; \forall A \in Type v,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{PartialOrder}\left(A\right)] \forall a : A, \operatorname{IsExtension}\left(P, \operatorname{Lex}\left(\operatorname{Prod}\left(P, A\right)\right)\right) \land \operatorname{Setoid}.IsPartition\left(\operatorname{Set}.range\left(p \mapsto \operatorname{lexFiber}\left(p\right)\right)\right) \land (\forall p \in P,\; \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(A, \operatorname{lexFiber}\left(p\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiberExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The base map is a section of first projection. Each literal fiber is the equivalence class of the corresponding base image for the kernel setoid of that projection. These classes partition the whole carrier. If P is empty, the carrier and the family of parts are both empty.

Taking A to be the natural numbers and the distinguished point to be zero gives an induced extension of every partial order and an omega partition in the original IsExtension and OmegaPartitionable predicates.

For any nonzero ordinal α in universe v, take A = α.ToType and choose the point represented by zero. The base may be in any independent universe u. Each part lies in universe max(u,v) and its inherited strict order has type Ordinal.lift to that universe applied to α. Lifting the ambient carrier upward again replaces each part by its preimage under ULift.down and lifts the order type accordingly. This covers α = 1, successors, limits and uncountable ordinals. The family is a skeleton in the sense of Definition 2.33 because it is disjoint and each point itself witnesses cofinality in its own part.

The construction formalizes the existence proposition and the extension clause of the skeleton corollary in the revision-2 note by Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of Singapore and ChronoAI Pte Ltd, Singapore). The countable partition theorem and the general partition and lifting results remain credited to Remi Salinas Schmeis.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexBaseEmbedding`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiber`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiberExtension`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiberOrderIso`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation](SalinasSchmeisOmegaChainExtensionRefutation.md)
