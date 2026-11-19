# Countable cofinal partitions and their induced extensions

## Abstract

Cofinal partitions of the naturals and inherited partitions of two poset extensions.

**Theorem 1.1 (Residue classes for a positive modulus).**

$$\forall m \in \mathbb{N},\; 0 < m \Rightarrow \operatorname{IsCofinalNatPartition}\left(\operatorname{residuePart}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.residuePartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The part indexed by i consists of i + m k for k in the naturals, where i < m and m is positive. Euclidean division recovers both the index i and the quotient k from a point of the part. For each index the range is infinite and therefore cofinal in the naturals. Modulus one gives the whole set of naturals as a single part.

**Theorem 1.2 (Parts indexed by the exponent of two).**

$$\operatorname{IsCofinalNatPartition}\left(twoAdicPart\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.twoAdicPartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The part indexed by i is the range of k mapped to 2^i (2 k + 1) - 1. The argument of subtraction is positive. Factor the successor of a natural into a power of two and an odd factor. Its exponent is determined by the factorization and gives the unique part. For each index the range is infinite and cofinal.

**Theorem 1.3 (A cofinal partition for each nonempty countable index type).**

$$\forall I \in Type u,\; [\operatorname{Nonempty}\left(I\right)] [\operatorname{Countable}\left(I\right)] \exists S \in I \to \operatorname{Set}\left(\mathbb{N}\right),\; \operatorname{IsCofinalNatPartition}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.countablePartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Transport the residue parts along an equivalence with a finite index type when the index is finite. Transport the two-adic parts along an equivalence with the naturals when it is infinite. Every natural belongs to exactly one indexed part and each part is infinite and cofinal. A positive finite cardinality follows from the nonempty hypothesis. An empty index type cannot cover the naturals.

**Theorem 1.4 (The partition of the ordinal sum U).**

$$\forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{Nonempty}\left(P\right)] [\operatorname{Countable}\left(P\right)] \operatorname{IsExtension}\left(P, \operatorname{U}\left(P\right)\right) \land\\\exists S \in P \to \operatorname{Set}\left(\mathbb{N}\right),\; \operatorname{IsCofinalNatPartition}\left(S\right) \land\\\operatorname{IsPartition}\left(\operatorname{range}\left(\operatorname{ordinalSumPart}\left(S\right)\right)\right) \land\\\forall p \in P,\; \operatorname{IsOmegaChain}\left(\operatorname{ordinalSumPart}\left(S\right)\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.ordinalSumPartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

Use the ordinal sum of the original poset P followed by the naturals. The left inclusion preserves and reflects the order of P. Choose a cofinal partition of the right summand indexed by P. The part for p consists of its left image and the right images of the selected naturals.

Enumerate the selected infinite subset in its inherited order using Nat.Subtype.orderIsoOfNat. Send zero to the prepended point and each successor to the corresponding element of the increasing enumeration. Strictness at the prepended point and preservation along the tail give an induced copy of the naturals whose range is the literal part.

**Theorem 1.5 (The partition of the maximal-ray extension V).**

$$\forall P \in Type u,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{Countable}\left(P\right)] \forall a \in P \to \operatorname{MaximalPoints}\left(P\right),\; (\forall p \in P,\; p \le \operatorname{val}\left(\operatorname{a}\left(p\right)\right)) \Rightarrow\\\operatorname{IsExtension}\left(P, \operatorname{MaximalRayExtension}\left(P\right)\right) \land\\\exists S \in (m: \operatorname{MaximalPoints}\left(P\right)) \to \{p \in P \mid \operatorname{a}\left(p\right) = m\} \to \operatorname{Set}\left(\mathbb{N}\right),\; (\forall m \in \operatorname{MaximalPoints}\left(P\right),\; \operatorname{IsCofinalNatPartition}\left(\operatorname{S}\left(m\right)\right)) \land\\\operatorname{IsPartition}\left(\operatorname{range}\left(\operatorname{maximalRayPart}\left(a, S\right)\right)\right) \land\\\forall p \in P,\; \operatorname{IsOmegaChain}\left(\operatorname{maximalRayPart}\left(a, S\right)\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.maximalRayPartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Remi Salinas Schmeis (2026). *General Criterion for a Poset to Admit a Partition Into omega-Chains*. URL: <https://arxiv.org/abs/2610.29056v1>.

*Commentary.*

The carrier consists of P and a separate natural ray over each maximal point m. The base keeps its order. A base point is below a ray point exactly when it is below m in P. Rays have their natural order and distinct maximal indices are incomparable. No ray point is below a base point.

Take an assignment a sending each p to a maximal point above it. It fixes each maximal point, so its fiber over that point is nonempty. Each assignment fiber is countable as a subtype. Partition the literal ray over m by the assignment fiber and prepend p to the selected tail on the ray over a(p). The ray index and the unique assigned point within that ray determine the part of every ray point. A base point lies only in its own part.

The ordinal sum and maximal-ray partitions are the two constructions used in the bounded-height theorem of the revision-2 note by Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of Singapore and ChronoAI Pte Ltd, Singapore). The maximal-ray construction allows countably infinitely many maximal points. These partitions provide admissibility for the comparison targets.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.countablePartition`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.maximalRayPartition`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.ordinalSumPartition`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.residuePartition`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions.twoAdicPartition`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension](SalinasSchmeisLexicographicFiberExtension.md)
