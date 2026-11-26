# Extensions by lexicographic fibers

## Abstract

Lexicographic extensions, inherited fiber partitions and explicit Noetherian lifting.

**Definition 1.1 (The first-coordinate fiber).**

$$\forall P \in Type u,\; \forall A \in Type v,\; \forall p \in P,\; \operatorname{lexFiber}\left(p\right) = \{x \in \operatorname{Lex}\left(\operatorname{Prod}\left(P, A\right)\right) \mid \operatorname{ofLex}\left(x\right).1 = p\}$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The carrier is Lex(Prod(P,A)), with the lexicographic partial order supplied by Mathlib. A fiber is the literal subset on which the first coordinate equals the index, with the order inherited from the product.

**Definition 1.2 (The inherited fiber order).**

$$\forall P \in Type u,\; \forall A \in Type v,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{PartialOrder}\left(A\right)] \forall p \in P,\; \forall a \in A,\; (\operatorname{lexFiberOrderIso}\left(p\right)\left(a\right)).val = \operatorname{toLex}\left((p, a)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiberOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Insert the second coordinate at the fixed first coordinate. The inverse reads the second coordinate, and the strict first-coordinate comparison is impossible within the fiber. The resulting comparison is exactly the comparison in A.

## The literal fiber partition

$$
\forall P \in Type u,\; \forall A \in Type v,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{PartialOrder}\left(A\right)] \forall a : A, \operatorname{IsExtension}\left(P, \operatorname{Lex}\left(\operatorname{Prod}\left(P, A\right)\right)\right) \land \operatorname{Setoid}.IsPartition\left(\operatorname{Set}.range\left(p \mapsto \operatorname{lexFiber}\left(p\right)\right)\right) \land (\forall p \in P,\; \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(A, \operatorname{lexFiber}\left(p\right)\right)\right))
$$

For the fixed point a of A, the map p ↦ toLex(p,a) preserves and reflects the order by the lexicographic comparison law. The map is a section of first projection. Each literal fiber is the kernel class of the corresponding base image by Setoid.mem_classes, and every kernel class is a fiber by Setoid.classes_ker_subset_fiber_set. Setoid.isPartition_classes therefore gives a partition of the whole carrier. If P is empty, the carrier and the family of parts are both empty.

Taking A to be the natural numbers and the distinguished point to be zero gives an induced extension of every partial order and an omega partition in the original IsExtension and OmegaPartitionable predicates.

For any nonzero ordinal α in universe v, take A = α.ToType and choose the point represented by zero. The base may be in any independent universe u. Each part lies in universe max(u,v) and its inherited strict order has type Ordinal.lift to that universe applied to α. Lifting the ambient carrier upward again replaces each part by its preimage under ULift.down and lifts the order type accordingly. This covers α = 1, successors, limits and uncountable ordinals. The family is a skeleton in the sense of Definition 2.33 because it is disjoint and each point itself witnesses cofinality in its own part.

The construction formalizes the existence proposition and the extension clause of the skeleton corollary in the revision-2 note by Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of Singapore and ChronoAI Pte Ltd, Singapore). The countable partition theorem and the general partition and lifting results remain credited to Remi Salinas Schmeis.

**Theorem 1.3 (Lifting Noetherian subsets of the natural-number extension).**

$$\forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] \forall K \in \operatorname{Set}\left(\operatorname{Lex}\left(\operatorname{Prod}\left(P, \mathbb{N}\right)\right)\right),\; (\forall C \in \operatorname{Set}\left(\operatorname{Lex}\left(\operatorname{Prod}\left(P, \mathbb{N}\right)\right)\right),\; C \subseteq K \Rightarrow \neg \operatorname{IsOmegaChain}\left(C\right)) \Rightarrow\\\exists b \in P \to \mathbb{N},\; (\forall p \in P,\; \operatorname{Finite}\left(\{n \in \mathbb{N} \mid \operatorname{toLex}\left((p, n)\right) \in K\}\right)) \land\\(\forall p \in P,\; \{n \in \mathbb{N} \mid \operatorname{toLex}\left((p, n)\right) \in K\} = \emptyset \Rightarrow \operatorname{b}\left(p\right) = 0) \land\\(\forall p \in P,\; \operatorname{Nonempty}\left(\{n \in \mathbb{N} \mid \operatorname{toLex}\left((p, n)\right) \in K\}\right) \Rightarrow \exists m \in \mathbb{N},\; \operatorname{IsGreatest}\left(\{n \in \mathbb{N} \mid \operatorname{toLex}\left((p, n)\right) \in K\}, m\right) \land \operatorname{b}\left(p\right) = 1 + m) \land\\\exists L \in \operatorname{Embedding}\left(K, \{y \in \operatorname{Lex}\left(\operatorname{Prod}\left(P, \mathbb{N}\right)\right) \mid \exists x \in K,\; x < y\} \setminus K\right),\; \forall x \in K,\; \operatorname{val}\left(x\right) < \operatorname{val}\left(\operatorname{L}\left(x\right)\right) \land \operatorname{val}\left(\operatorname{L}\left(x\right)\right) = \operatorname{toLex}\left((\operatorname{fst}\left(\operatorname{ofLex}\left(\operatorname{val}\left(x\right)\right)\right), \operatorname{b}\left(\operatorname{fst}\left(\operatorname{ofLex}\left(\operatorname{val}\left(x\right)\right)\right)\right) + \operatorname{snd}\left(\operatorname{ofLex}\left(\operatorname{val}\left(x\right)\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexNatFiberLifting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Let E be the lexicographic product of an arbitrary partial order with the natural numbers. The premise says that K contains no subset order-isomorphic to the natural numbers with its inherited order. An infinite section of K would have an increasing enumeration by Nat.Subtype.orderIsoOfNat. Composing it with lexFiberOrderIso and taking its inherited range in E would give such a subset of K. Thus every section is finite. P and K may be uncountable.

An empty section has offset zero. In a nonempty section the offset is one plus its maximum. Adding this offset to the second coordinate sends an input above the entire section. The image lies outside K, and the original input witnesses membership in the strict upset. Equal images give the same first coordinate and therefore the same offset, which can then be cancelled from the second coordinates. This gives a single injection on K, including the empty injection when K is empty.

Every point of E has a strict successor obtained by adding one in its fiber. The no-maximal-element condition is vacuous when P is empty. The global injection and its strict upwardness give the lifting property of Definition 2.26. Its injectivity gives the cardinal inequality of local shortness in Definition 2.14. This is the explicit lifting corollary in the revision-2 note by Haobo Ma and Wenlin Zhang. The general equivalence in Theorem 2.27 is due to Remi Salinas Schmeis.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiber`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexFiberOrderIso`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.lexNatFiberLifting`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation](SalinasSchmeisOmegaChainExtensionRefutation.md)
