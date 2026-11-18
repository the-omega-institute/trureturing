# Least omega-chain extensions at bounded finite height

## Abstract

Least extensions at bounded finite height and the finite skeleton obstruction.

**Definition 1.1 (Parts of a prescribed inherited order type).**

$$\forall A \in Type a,\; [\operatorname{PartialOrder}\left(A\right)] \forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] \operatorname{PartitionableBy}\left(A, P\right) \Leftrightarrow \exists D \in \operatorname{Set}\left(\operatorname{Set}\left(P\right)\right),\; \operatorname{IsPartition}\left(D\right) \land \forall C \in \operatorname{Set}\left(P\right),\; C \in D \Rightarrow \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(A, C\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.PartitionableBy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The family consists of actual subsets. IsPartition demands nonempty parts, unique membership and whole-carrier coverage. Each part carries its induced order. For A equal to the natural numbers this is OmegaPartitionable. For A equal to the dual of the natural numbers this expresses an omega-star partition.

**Definition 1.2 (Leastness among partitionable extensions).**

$$\forall A \in Type a,\; [\operatorname{PartialOrder}\left(A\right)] \forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] \forall Q \in Type v,\; [\operatorname{PartialOrder}\left(Q\right)] \operatorname{IsLeastExtension}\left(w, A, P, Q\right) \Leftrightarrow \operatorname{IsExtension}\left(P, Q\right) \land \operatorname{PartitionableBy}\left(A, Q\right) \land\\\forall X \in Type w,\; \forall xOrder \in \operatorname{PartialOrder}\left(X\right),\; \operatorname{IsExtension}\left(P, X, xOrder\right) \Rightarrow \operatorname{PartitionableBy}\left(A, X, xOrder\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{OrderEmbedding}\left(Q, X, xOrder\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.IsLeastExtension` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Both base maps are induced order embeddings. Comparison only asks for an order embedding of Q into X. There is no equation involving the two base maps. Every partial order on a carrier in universe w is eligible as X if it extends P and has the indicated partition.

**Definition 1.3 (Least candidates in independent universes).**

$$\forall A \in Type a,\; [\operatorname{PartialOrder}\left(A\right)] \forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] \operatorname{HasLeastExtension}\left(v, w, A, P\right) \Leftrightarrow \exists Q \in Type v,\; \exists qOrder \in \operatorname{PartialOrder}\left(Q\right),\; \operatorname{IsLeastExtension}\left(w, A, P, Q, qOrder\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.HasLeastExtension` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The level u is for P, v is for the candidate and w is for comparisons. These levels are fixed independently. An order on Q is part of the witness. For the natural chain as A, taking this predicate for every P gives the telescope of the original question.

**Theorem 1.4 (The ordinal sum as an explicit least extension).**

$$\forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{Countable}\left(P\right)] \forall t \in P,\; \operatorname{IsTop}\left(t\right) \Rightarrow \operatorname{IsLeastExtension}\left(w, \mathbb{N}, P, \operatorname{OrdinalSum}\left(P, \mathbb{N}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.ordinalSum_isLeastExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Reuse ordinalSumPartition for the actual sum U of P followed by the naturals. In a competing extension X, find the partition part containing the image of the greatest element t. Shift the natural enumeration of this part to start one step after the index of the image of t. The resulting strict tail lies strictly above every base image.

On the left summand use the supplied base embedding, and on the right summand use the strict tail. Each map preserves and reflects comparisons within its summand. Every left image is below each right image, and antisymmetry forbids a comparison in the other direction.

**Theorem 1.5 (The greatest-element implication at every candidate level).**

$$\forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{Countable}\left(P\right)] \forall t \in P,\; \operatorname{IsTop}\left(t\right) \Rightarrow \operatorname{HasLeastExtension}\left(v, w, \mathbb{N}, P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.hasLeastOmegaExtension_of_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

A countable carrier has a Mathlib Shrink copy in the prescribed universe. orderIsoShrink transports the order. Transport each literal partition part by its image and compose its inherited order isomorphism. Surjectivity gives coverage, and injectivity gives uniqueness of parts from the original family. Compose the distinguished base embedding with the isomorphism and every comparison with its inverse. This argument needs no height bound.

**Theorem 1.6 (The countable bounded-height classification).**

$$\forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{Nonempty}\left(P\right)] [\operatorname{Countable}\left(P\right)] \operatorname{chainHeight}\left(\operatorname{univ}\left(P\right), \operatorname{le}\left(P\right)\right) \neq \infty \Rightarrow\\\operatorname{HasLeastExtension}\left(v, w, \mathbb{N}, P\right) \Leftrightarrow \exists t \in P,\; \operatorname{IsTop}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.hasLeastOmegaExtension_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The chain height is the supremum of the extended natural cardinalities of chains. A finite bound rules out every embedded increasing omega sequence and makes the greatest chain size attained. Applying well-foundedness of the reverse strict order to the upper set of each p gives a maximal point above p. If the maximal point were unique it would be greatest.

Use the literal ordinal sum U and the literal maximal-ray extension V. Reuse ordinalSumPartition and maximalRayPartition with the chosen maximal-above assignment. Their countable carriers have actual order-isomorphic copies in the comparison universe. The construction allows countably infinitely many maximal points.

Any least candidate embeds into both actual models by composing the comparison embeddings with the inverses of the chosen order isomorphisms. The image of a strict omega tail in U leaves P, stays in the natural summand and is cofinal there. Reflecting an upper bound built in such a tail proves that the candidate is upward directed. In V an omega tail also leaves P and reaches a ray over some m. The only upper bounds of that ray point are on the same ray. Directedness then puts every image point either below m in the base or on that ray.

Compose the induced copy of P in the candidate with the embedding into V. Each maximal point of P has another incomparable maximal point. Every ray point and the base point m are comparable with every point in the concentrated image, so the images of the maximal points lie strictly below m. The same is true of all base images by maximal-above. Transport an attained h-element chain of P through this induced copy below m. Adjoining m yields h plus one elements in a chain of P.

For a finite nonempty poset, the number of points bounds chain sizes. A nonempty countable antichain has height one and a greatest point exactly when it is a singleton. One bottom point below at least two incomparable maxima has height two and lacks a greatest point, including when the set of maxima is countably infinite.

The empty poset is least using the empty partition and its unique embeddings. A singleton has a greatest point, so the two-point antichain has minimum counterexample cardinality. A nonempty finite chain embeds into the naturals by its increasing finite enumeration. Any admissible extension of that chain contains an actual partition part, which gives an embedding from the naturals. Thus the naturals are themselves a least extension of every nonempty finite chain.

For the dual statement keep the same partition family and dualize its inherited isomorphisms. Dualize both ends of every base and comparison embedding. Each arbitrary comparison target can be dualized back, and dualizing twice restores the original data. Chain cardinalities are preserved. This gives the least-element classification for omega-star partitions, including finite, antichain, fork, finite-chain and empty cases. It also gives the reversed Rays and Tail obstruction, including the dual fork and the two-point antichain, and transports the lexicographic fiber construction for arbitrary base posets.

The naturals have the single full part as an omega partition. The identity makes them an admissible self-extension, and every competing extension already admits an embedding of the naturals. Any n has a larger point n plus one, and the initial segments have unbounded finite sizes. The dual natural order is least for omega-star partitions and has no least element. These are boundary cases for the uniform height hypothesis.

This is the bounded-height theorem and its applications in the revision-2 note by Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of Singapore and ChronoAI Pte Ltd, Singapore). The original Fork, Rays and Tail refutation and its settlement retain their credit. Remi Salinas Schmeis owns the posing question and the cited prior partition and lifting results.

**Theorem 1.7 (A cofinal inherited chain without a partition).**

$$\forall n \in \mathbb{N},\; 2 \le n \Rightarrow\\\operatorname{IsCofinal}\left(\operatorname{Ioi}\left(0 : \operatorname{Fin}\left(n + 1\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{Fin}\left(n\right), \operatorname{Ioi}\left(0 : \operatorname{Fin}\left(n + 1\right)\right)\right)\right) \land\\\neg \operatorname{PartitionableBy}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.finiteSkeletonObstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

For each natural n at least two, use the chain Fin(n+1) with its usual order. The strict interval above zero is the literal tail {1, …, n}, isomorphic to Fin(n) under successor. It contains the greatest point, so the one-member family consisting of this interval is pairwise disjoint with a cofinal union, as in Definition 2.33.

In any proposed partition, take the inherited isomorphism from Fin(n) to each part. The product of the type of parts with Fin(n) maps bijectively to Fin(n+1). Surjectivity uses coverage and injectivity uses unique membership followed by injectivity within the part. If there are m parts, counting gives n+1 = nm, so n divides 1. This contradicts n at least two.

For n = 1, singleton parts partition every partial order. A one-point order has no inherited two-point chain and therefore no 2-skeleton. The finite obstruction is the second clause of the skeleton corollary in revision 2 by Haobo Ma and Wenlin Zhang. Its first clause, concerning extensions for every nonzero ordinal, is in the lexicographic fiber document.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.HasLeastExtension`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.IsLeastExtension`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.PartitionableBy`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.finiteSkeletonObstruction`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.hasLeastOmegaExtension_iff`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.hasLeastOmegaExtension_of_top`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.ordinalSum_isLeastExtension`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions](SalinasSchmeisCountablePartitions.md)
