# Refutation of the least omega-chain-partitionable extension question

## Abstract

Question 2.32 has no universal least omega-chain-partitionable extension.

**Definition 1.1 (Parts order-isomorphic to omega).**

$$\forall P \in Type,\; [\operatorname{PartialOrder}\left(P\right)] \forall C \in \operatorname{Set}\left(P\right),\; \operatorname{IsOmegaChain}\left(C\right) = \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(Nat, C\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.IsOmegaChain` (`✓ std3`).

*Citation.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Page 2: “An ω-chain of a poset P is a subset of P that is order-isomorphic to ω under the ordering inherited from P.” The formula uses the inherited order on the subtype C.

**Definition 1.2 (Partitions into omega-chains).**

$$\forall P \in Type,\; [\operatorname{PartialOrder}\left(P\right)] \operatorname{OmegaPartitionable}\left(P\right) = (\exists D \in \operatorname{Set}\left(\operatorname{Set}\left(P\right)\right),\; (\operatorname{Setoid}.IsPartition\left(D\right)) \land (\forall C \in \operatorname{Set}\left(P\right),\; (C \in D) \Rightarrow (\operatorname{IsOmegaChain}\left(C\right))))$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.OmegaPartitionable` (`✓ std3`).

*Citation.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Question 2.3, page 2: “Given a poset P with no maximal element, when can the maximal family D of disjoint ω-chains in P given by Lemma 2.1 be taken such that ⋃D = P? That is, when can P be partitioned into ω-chains?” The formula records a covering disjoint family whose members satisfy IsOmegaChain.

**Definition 1.3 (Induced order extension).**

$$\forall P \in Type,\; \forall Q \in Type,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{PartialOrder}\left(Q\right)] \operatorname{IsExtension}\left(P, Q\right) = \operatorname{Nonempty}\left(\operatorname{OrderEmbedding}\left(P, Q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.IsExtension` (`✓ std3`).

*Citation.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

An extension is represented by an order embedding, so the original order is preserved and reflected.

**Definition 1.4 (Question 2.32).**

$$claim = (\forall P \in Type,\; \forall pOrder \in \operatorname{PartialOrder}\left(P\right),\; \exists Q \in Type,\; \exists qOrder \in \operatorname{PartialOrder}\left(Q\right),\; (\operatorname{IsExtension}\left(P, Q, pOrder, qOrder\right)) \land ((\operatorname{OmegaPartitionable}\left(Q, qOrder\right)) \land (\forall Qprime \in Type,\; \forall qOrderPrime \in \operatorname{PartialOrder}\left(Qprime\right),\; (\operatorname{IsExtension}\left(P, Qprime, pOrder, qOrderPrime\right)) \Rightarrow ((\operatorname{OmegaPartitionable}\left(Qprime, qOrderPrime\right)) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{OrderEmbedding}\left(Q, Qprime, qOrder.toLE, qOrderPrime.toLE\right)\right))))))$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.claim` (`✓ std3`).

*Citation.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Question 2.32, page 14: “Let P be a poset. Does there exist a minimal extension Q of P which can be partitioned into ω-chains? Here by minimal we mean that if Q′ is any extension of P which can be partitioned into ω-chains, then Q is order-isomorphic to a subposet of Q′.” The encoding uses an induced order embedding for extension and a setoid partition whose parts are order-isomorphic to omega.

**Theorem 1.5 (Separated rays and a merged tail are incompatible).**

$$\neg (\forall P \in Type,\; \forall pOrder \in \operatorname{PartialOrder}\left(P\right),\; \exists Q \in Type,\; \exists qOrder \in \operatorname{PartialOrder}\left(Q\right),\; (\operatorname{IsExtension}\left(P, Q, pOrder, qOrder\right)) \land ((\operatorname{OmegaPartitionable}\left(Q, qOrder\right)) \land (\forall Qprime \in Type,\; \forall qOrderPrime \in \operatorname{PartialOrder}\left(Qprime\right),\; (\operatorname{IsExtension}\left(P, Qprime, pOrder, qOrderPrime\right)) \Rightarrow ((\operatorname{OmegaPartitionable}\left(Qprime, qOrderPrime\right)) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{OrderEmbedding}\left(Q, Qprime, qOrder.toLE, qOrderPrime.toLE\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/salinas-omega-chain-extension` (refuted) by `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"salinas-omega-chain-extension","declaration_gid":"D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The separated-ray order Rays has carrier Bool × ℕ. Its relation is x ≤ y exactly when x = (false, 0) or both x.1 = y.1 and x.2 ≤ y.2. The partition consists of the two full ranges {(false, n) | n ∈ ℕ} and {(true, n) | n ∈ ℕ}. They are disjoint and cover Rays, and the maps n ↦ (false, n) and n ↦ (true, n) are order isomorphisms onto the respective ranges with inherited order. The fork's root and two branches map to (false, 0), (false, 1) and (true, 0).

The order Tail has carrier ℕ, with x ≤ y exactly when the usual natural-number comparison holds and (x, y) ≠ (1, 2). Its partition consists of the ranges {2n | n ∈ ℕ} and {2n + 1 | n ∈ ℕ}. They are disjoint and cover Tail. The maps n ↦ 2n and n ↦ 2n + 1 are order isomorphisms onto these inherited even and odd chains: the removed comparison joins different parts. The fork's root and two branches map to 0, 1 and 2.

The three-element fork thus embeds into two omega-chain-partitionable orders. In the separated-ray order, two points with a common upper bound are comparable. In the tail order obtained by removing the comparison 1 ≤ 2, a strict successor of one incomparable point is above the other. An omega-chain partition supplies such a strict successor, and order embeddings transfer the resulting comparisons back to the fork, producing a contradiction.

The literature screen is partial. The primary source and its version history, successful arXiv author and text queries, MathOverflow and Zenodo searches, public formal-conjecture snapshots and repository results identified no matching settlement in the inspected scope. Citation enumeration was unavailable, several Zenodo endpoints were blocked, and the original MacNeille completion article was not independently read. Those gaps and literature completeness remain ASSUMED-UNVERIFIED; no worldwide novelty or exhaustive coverage is asserted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.IsExtension`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.IsOmegaChain`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.OmegaPartitionable`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.claim`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.result`
