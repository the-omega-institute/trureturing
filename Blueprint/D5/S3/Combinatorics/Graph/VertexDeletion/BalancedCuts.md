# Balanced cuts optimize pairwise and largest-component damage

## Abstract

Balanced cuts uniquely maximize pair and largest-component damage.

**Theorem 1.1 (Uniform prefix le q).**

$$\forall \{b k q : \mathbb{N}\}, 2 \cdot b \cdot (k + 2) \leq q \Rightarrow b \cdot (k + 2) \leq q$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_prefix_le_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The size of the intact prefix fits inside one balanced part.

**Theorem 1.2 (Uniform prefix lt q).**

$$\forall \{b k q : \mathbb{N}\}, 2 \leq b \Rightarrow 2 \cdot b \cdot (k + 2) \leq q \Rightarrow b \cdot (k + 2) < q$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_prefix_lt_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict inequality leaves room for the positive first tail run.

**Definition 1.3 (Uniform balanced deletion).**

$$\mathrm{uniformBalancedDeletion} : \{b k q : \mathbb{N}\} \Rightarrow 2 \cdot b \cdot (k + 2) \leq q \Rightarrow \mathrm{Finset} (\mathrm{UniformVertex} b k q)$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniformBalancedDeletion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delete the b prescribed tail positions, each separated from the next by q survivors.

**Theorem 1.4 (Uniform balanced deletion card).**

$$\forall \{b k q : \mathbb{N}\} (\mathrm{hq} : 2 \cdot b \cdot (k + 2) \leq q), (\mathrm{uniformBalancedDeletion} \mathrm{hq}).\mathrm{card} = b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered tail positions are distinct, so the prescribed cut has exactly b deletions.

**Theorem 1.5 (Uniform balanced deletion profile).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\} (\mathrm{hb} : 2 \leq b),\\1 \leq k \Rightarrow\\\forall (\mathrm{hq} : 2 \cdot b \cdot (k + 2) \leq q),\\\mathrm{have} D : = \mathrm{uniformBalancedDeletion} \mathrm{hq};\\\mathrm{let} G : = \mathrm{survivorGraph} (\mathrm{host} (\mathrm{uniformHub} b)) D;\\(\mathrm{Function}.\mathrm{Bijective} \lambda i =>\\\mathrm{TailRun}.\mathrm{component} (\mathrm{uniformHub} b) (\mathrm{uniformBalancedDeletion} \mathrm{hq})\\(\mathrm{uniformBalancedRun} \mathrm{hb} \mathrm{hq} i)) \land\\(\forall (i : \mathrm{Fin} (b + 1)),\\\mathrm{coe}(\mathrm{uniformBalancedRun} \mathrm{hb} \mathrm{hq} i).\mathrm{last} + 1 - \mathrm{coe}(\mathrm{uniformBalancedRun} \mathrm{hb} \mathrm{hq} i).\mathrm{first} =\\\mathrm{if} \mathrm{coe}i = 0 \mathrm{then} q - b \cdot (k + 2) \mathrm{else} q) \land\\\mathrm{Fintype}.\mathrm{card} G.\mathrm{ConnectedComponent} = b + 1 \land \forall (C : G.\mathrm{ConnectedComponent}), C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card} = q\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut positions realize b+1 runs. The first run carries the intact prefix and its leaves, so every actual component has size q.

**Theorem 1.6 (Component profile score formulas).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (H : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} H.\mathrm{Adj}]\\(D : \mathrm{Finset} V),\\\mathrm{let} G : = \mathrm{survivorGraph} H D;\\\mathrm{pcDamage} H D = (\mathrm{Fintype}.\mathrm{card} V).\mathrm{choose} 2 - \sum C, C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card}.\mathrm{choose} 2\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.component_profile_score_formulas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair sum and the largest part can be computed directly on the component supports.

**Theorem 1.7 (Balanced pair target positive).**

$$\forall \{m q n : \mathbb{N}\}, 2 \leq m \Rightarrow 0 < q \Rightarrow m \cdot q \leq n \Rightarrow m \cdot q.\mathrm{choose} 2 < n.\mathrm{choose} 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.balanced_pair_target_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at least two positive equal parts, the within-part pairs omit every cross-part pair.

**Theorem 1.8 (Scores of equal component sizes).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (H : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} H.\mathrm{Adj}]\\(D : \mathrm{Finset} V) (m q : \mathbb{N}),\\\mathrm{Fintype}.\mathrm{card} (\mathrm{survivorGraph} H D).\mathrm{ConnectedComponent} = m \Rightarrow\\0 < m \Rightarrow\\(\forall (C : (\mathrm{survivorGraph} H D).\mathrm{ConnectedComponent}), C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card} = q) \Rightarrow\\\mathrm{pcDamage} H D = (\mathrm{Fintype}.\mathrm{card} V).\mathrm{choose} 2 - m \cdot q.\mathrm{choose} 2 \land\\\mathrm{lccDamage} H D = \mathrm{Fintype}.\mathrm{card} V - q\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.scores_of_equal_component_sizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A component-cardinality equivalence gives the score values of the equal-part profile.

**Theorem 1.9 (Uniform balanced deletion scores).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\1 \leq k \Rightarrow\\\forall (\mathrm{hq} : 2 \cdot b \cdot (k + 2) \leq q),\\\mathrm{have} n : = \mathrm{Fintype}.\mathrm{card} (\mathrm{UniformVertex} b k q);\\\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b)) (\mathrm{uniformBalancedDeletion} \mathrm{hq}) =\\n.\mathrm{choose} 2 - (b + 1) \cdot q.\mathrm{choose} 2 \land\\\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b)) (\mathrm{uniformBalancedDeletion} \mathrm{hq}) =\\n - q\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_scores` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the b+1 components of size q to obtain both target scores.

**Theorem 1.10 (Uniform balanced deletion unique optimizer).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\1 \leq k \Rightarrow\\\forall (\mathrm{hq} : 2 \cdot b \cdot (k + 2) \leq q) (D : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{let} H : = \mathrm{host} (\mathrm{uniformHub} b);\\\mathrm{have} B : = \mathrm{uniformBalancedDeletion} \mathrm{hq};\\\mathrm{pcDamage} H D \leq \mathrm{pcDamage} H B \land\\\mathrm{lccDamage} H D \leq \mathrm{lccDamage} H B \land\\(\mathrm{pcDamage} H D = \mathrm{pcDamage} H B \lor\\\mathrm{lccDamage} H D = \mathrm{lccDamage} H B \iff\\D = B)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_unique_optimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Too few positive tail runs give strict comparisons. With the full count, equality requires all parts to have size q and the ordered cuts are then determined.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.balanced_pair_target_positive`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.component_profile_score_formulas`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.scores_of_equal_component_sizes`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniformBalancedDeletion`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_profile`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_scores`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_balanced_deletion_unique_optimizer`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_prefix_le_q`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.uniform_prefix_lt_q`
- Dependency: [D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents](TailComponents.md)
