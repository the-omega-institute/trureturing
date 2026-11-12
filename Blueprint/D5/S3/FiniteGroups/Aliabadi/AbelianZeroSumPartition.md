# Finite abelian Erdős–Ginzburg–Ziv extraction and partitions

## Abstract

Finite abelian zero-sum extraction and exact partitions preserve the original label support.

**Theorem 1.1 (Order-length extraction in every finite abelian group).**

$$\forall G \in Typeu,\; \forall group \in \operatorname{AddCommGroup}\left(G\right),\; \forall finite \in \operatorname{Finite}\left(G\right),\; \forall I \in Typev,\; \forall a \in I \to G,\; \forall s \in \operatorname{Finset}\left(I\right),\; 2\cdot\operatorname{NatCard}\left(G\right)-1 \le \operatorname{card}\left(s\right) \Rightarrow \left(\exists t \in \operatorname{Finset}\left(I\right),\; t \subseteq s \land \left(\operatorname{card}\left(t\right) = \operatorname{NatCard}\left(G\right) \land \operatorname{sum}\left(t, a\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition.exists_zero_sum_card` (`✓ std3`). ∎

*Citation.* P. Erdős; A. Ginzburg; A. Ziv (1961). *Theorem in the additive number theory*. URL: <https://users.renyi.hu/~p_erdos/1961-25.pdf>.

*Commentary.*

G and the label type I inhabit independent universes u and v. G is an additive commutative group with a Finite instance; I need not be finite. For any labeling a and finite support s with at least 2 Nat.card(G) minus 1 labels, a subset of exactly Nat.card(G) original labels has zero sum. Values may repeat, and the trivial group is included.

The cyclic seed is Mathlib's ZMod.erdos_ginzburg_ziv. For a direct product, greedy extraction builds 2q minus 1 pairwise disjoint first-coordinate zero-sum blocks of size n in the exact unused support. Apply second-factor extraction to the second-coordinate sums of these same blocks and union the q selected blocks. Disjointness gives nq original labels. Induction over Gordon.Chain and Gordon.finite_abelian_presentation supplies arbitrary finite abelian groups, and the additive equivalence transports sums without relabeling. The arbitrary finite abelian theorem is stated in the primary article's final paragraph.

**Theorem 1.2 (Exactly m zero-sum blocks on the original labels).**

$$\forall G \in Typeu,\; \forall group \in \operatorname{AddCommGroup}\left(G\right),\; \forall finite \in \operatorname{Finite}\left(G\right),\; \forall I \in Typev,\; \forall a \in I \to G,\; \forall s \in \operatorname{Finset}\left(I\right),\; \forall m \in \mathbb{N},\; \left(\operatorname{card}\left(s\right) = m\cdot\operatorname{NatCard}\left(G\right) \land \operatorname{sum}\left(s, a\right) = 0\right) \Rightarrow \left(\exists B \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(I\right),\; \left(\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{B}\left(j\right) \subseteq s\right) \land \left(\left(\forall j \in \operatorname{Fin}\left(m\right),\; \forall k \in \operatorname{Fin}\left(m\right),\; \left(\neg j = k\right) \Rightarrow \operatorname{Disjoint}\left(\operatorname{B}\left(j\right), \operatorname{B}\left(k\right)\right)\right) \land \left(\operatorname{biUnion}\left(\operatorname{univ}\left(\operatorname{Fin}\left(m\right)\right), B\right) = s \land \left(\left(\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{card}\left(\operatorname{B}\left(j\right)\right) = \operatorname{NatCard}\left(G\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{sum}\left(\operatorname{B}\left(j\right), a\right) = 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition.exists_zero_sum_partition` (`✓ std3`). ∎

*Citation.* P. Erdős; A. Ginzburg; A. Ziv (1961). *Theorem in the additive number theory*. URL: <https://users.renyi.hu/~p_erdos/1961-25.pdf>.

*Commentary.*

If the original support has cardinality m Nat.card(G) and total zero, there is a function B from Fin m to Finset I. Each B(j) is a subset of s, distinct indices have disjoint blocks, the union over all indices equals s, and every block has cardinality Nat.card(G) and sum zero. There is no cyclicity, distinct-value, nontriviality, extraction-certificate or Fintype(I) hypothesis.

For m=0 the cardinality equation forces an empty support. For one block use the whole remaining support. With at least two blocks, the extraction theorem removes one zero-sum block and recursion applies to the exact complement. The complement retains both the required cardinality and zero total. Fin.cons adjoins the removed block, preserving the exact Fin m endpoint and the same original label support. This is the iterated consequence of the cited theorem needed for the finite-abelian subgroup partition criterion.

## References

- Truth anchor: `D5/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition.exists_zero_sum_card`
- Truth anchor: `D5/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition.exists_zero_sum_partition`
- Dependency: [D5/S3/FiniteGroups/GordonFullSet](../GordonFullSet.md)
