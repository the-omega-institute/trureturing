# Fixed-budget classification of transfers involving NC

## Abstract

Fixed-budget classification of objective transfers involving NC.

**Theorem 1.1 (Degree two common optimizer).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}],\\G.\mathrm{Connected} \Rightarrow\\G.\mathrm{maxDegree} \leq 2 \Rightarrow\\\forall (b : \mathbb{N}),\\2 \leq b \Rightarrow\\b < \mathrm{Fintype}.\mathrm{card} V \Rightarrow\\\exists D,\\D.\mathrm{card} = b \land\\\mathrm{ncDamage} G D = \mathrm{damageMaximum} (\mathrm{ncDamage} G) b \land\\\mathrm{pcDamage} G D = \mathrm{damageMaximum} (\mathrm{pcDamage} G) b \land\\\mathrm{lccDamage} G D = \mathrm{damageMaximum} (\mathrm{lccDamage} G) b\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.degree_two_common_optimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A spanning path order has at most one closing edge. Place the exact deletions so that the maximal feasible number of positive runs have balanced sizes.

**Theorem 1.2 (Degree two optimistic transfers eq one).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}],\\G.\mathrm{Connected} \Rightarrow\\G.\mathrm{maxDegree} \leq 2 \Rightarrow\\\forall (b : \mathbb{N}),\\2 \leq b \Rightarrow\\b < \mathrm{Fintype}.\mathrm{card} V \Rightarrow\\\forall (\mathrm{source} \mathrm{target} : \mathrm{Finset} V \Rightarrow \mathbb{N}),\\\mathrm{source} = \mathrm{ncDamage} G \lor \mathrm{source} = \mathrm{pcDamage} G \lor \mathrm{source} = \mathrm{lccDamage} G \Rightarrow\\\mathrm{target} = \mathrm{ncDamage} G \lor \mathrm{target} = \mathrm{pcDamage} G \lor \mathrm{target} = \mathrm{lccDamage} G \Rightarrow\\0 < \mathrm{damageMaximum} \mathrm{target} b \Rightarrow \mathrm{optimisticDamageRatio} \mathrm{source} \mathrm{target} b = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.degree_two_optimistic_transfers_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common optimizer attains the target maximum within the source-optimal set. Each ordered pair uses its own positive target guard.

**Definition 1.3 (Exact optimizer).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (\mathrm{score} : \mathrm{Finset} V \Rightarrow \mathbb{N}) (b : \mathbb{N}) (D : \mathrm{Finset} V), \mathrm{ExactOptimizer} \mathrm{score} b D \iff\\D.\mathrm{card} = b \land \mathrm{score} D = \mathrm{damageMaximum} \mathrm{score} b\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.ExactOptimizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deletion has exactly b vertices and attains the maximum of the specified score.

**Theorem 1.4 (Result).**

$$\begin{aligned}\forall (b : \mathbb{N}),\\2 \leq b \Rightarrow\\(\forall (\varepsilon : \mathbb{R}),\\0 < \varepsilon \Rightarrow\\\exists (k q : \mathbb{N}),\\1 \leq k \land\\2 \cdot b \cdot (k + 2) \leq q \land\\\mathrm{let} H : = \mathrm{uniformHost} b k q;\\H.\mathrm{IsTree} \land\\b < \mathrm{Fintype}.\mathrm{card} (\mathrm{UniformVertex} b k q) \land\\0 < \mathrm{damageMaximum} (\mathrm{ncDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{pcDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{lccDamage} H) b \land\\\forall (\mathrm{Dn} \mathrm{Dp} \mathrm{Dl} : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\\mathrm{ExactOptimizer} (\mathrm{ncDamage} H) b \mathrm{Dn} \Rightarrow\\\mathrm{ExactOptimizer} (\mathrm{pcDamage} H) b \mathrm{Dp} \Rightarrow\\\mathrm{ExactOptimizer} (\mathrm{lccDamage} H) b \mathrm{Dl} \Rightarrow\\\mathrm{damageRatio} (\mathrm{ncDamage} H) b \mathrm{Dp} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{ncDamage} H) b \mathrm{Dl} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{pcDamage} H) b \mathrm{Dn} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{lccDamage} H) b \mathrm{Dn} < \varepsilon) \land\\(\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}]\\(\Delta : \mathbb{N}),\\G.\mathrm{Connected} \Rightarrow\\b < \mathrm{Fintype}.\mathrm{card} V \Rightarrow\\3 \leq \Delta \Rightarrow\\G.\mathrm{maxDegree} \leq \Delta \Rightarrow\\0 < \mathrm{damageMaximum} (\mathrm{ncDamage} G) b \Rightarrow\\(\forall (D : \mathrm{Finset} V),\\\mathrm{ExactOptimizer} (\mathrm{pcDamage} G) b D \Rightarrow\\1 / \mathrm{coe}(b \cdot (\Delta - 1)) \leq \mathrm{damageRatio} (\mathrm{ncDamage} G) b D) \land\\\forall (D : \mathrm{Finset} V),\\\mathrm{ExactOptimizer} (\mathrm{lccDamage} G) b D \Rightarrow\\1 / \mathrm{coe}(b \cdot (\Delta - 1)) \leq \mathrm{damageRatio} (\mathrm{ncDamage} G) b D) \land\\(\forall (\mathrm{pc} : \mathrm{Bool}), \mathrm{sInf} (\mathrm{subcubicTreeOptimisticOutOfNC} b \mathrm{pc}) = 0) \land\\\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V)\\{}[\mathrm{DecidableRel} G.\mathrm{Adj}],\\G.\mathrm{Connected} \Rightarrow\\G.\mathrm{maxDegree} \leq 2 \Rightarrow\\b < \mathrm{Fintype}.\mathrm{card} V \Rightarrow\\(\exists (D : \mathrm{Finset} V),\\\mathrm{ExactOptimizer} (\mathrm{ncDamage} G) b D \land\\\mathrm{ExactOptimizer} (\mathrm{pcDamage} G) b D \land\\\mathrm{ExactOptimizer} (\mathrm{lccDamage} G) b D) \land\\\forall (\mathrm{source} \mathrm{target} : \mathrm{Finset} V \Rightarrow \mathbb{N}),\\\mathrm{source} = \mathrm{ncDamage} G \lor\\\mathrm{source} = \mathrm{pcDamage} G \lor \mathrm{source} = \mathrm{lccDamage} G \Rightarrow\\\mathrm{target} = \mathrm{ncDamage} G \lor\\\mathrm{target} = \mathrm{pcDamage} G \lor \mathrm{target} = \mathrm{lccDamage} G \Rightarrow\\0 < \mathrm{damageMaximum} \mathrm{target} b \Rightarrow \mathrm{optimisticDamageRatio} \mathrm{source} \mathrm{target} b = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Section 9 asks “whether the constants improve on trees or on bounded-degree graphs, or whether the NC directions remain vanishing there.” The theorem settles the registered fixed-budget NC clause. One tree witnesses all four comparisons at once. At fixed degree bound at least three, inbound ratios have the stated pointwise lower bound, while both optimistic outgoing ratios have infimum zero on subcubic trees. Degree at most two gives a common exact optimizer and ratio one for every positive-target optimistic transfer. Sharp positive constants and proportional budgets remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.ExactOptimizer`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.degree_two_common_optimizer`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.degree_two_optimistic_transfers_eq_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/Classification.result`
- Dependency: [D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds](DegreeBounds.md)
