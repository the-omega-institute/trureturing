# NC transfer bounds under degree constraints

## Abstract

Degree bounds and positive-target optimistic ratios for exact cuts.

**Theorem 1.1 (Survivor card).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (D : \mathrm{Finset} V),\\\mathrm{Fintype}.\mathrm{card} \mathrm{coe}(\mathrm{survivors} D) = \mathrm{Fintype}.\mathrm{card} V - D.\mathrm{card}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.survivor_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The survivors are the complement of the deletion finset.

**Theorem 1.2 (Component card eq).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}]\\(D : \mathrm{Finset} V),\\(\mathrm{componentSizes} G D).\mathrm{card} = \mathrm{Fintype}.\mathrm{card} (\mathrm{survivorGraph} G D).\mathrm{ConnectedComponent}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.component_card_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The size multiset has one entry per actual survivor component.

**Theorem 1.3 (Nc le budget mul degree sub one).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}],\\G.\mathrm{Connected} \Rightarrow\\\forall (\Delta : \mathbb{N}), G.\mathrm{maxDegree} \leq \Delta \Rightarrow \forall (b : \mathbb{N}) (D : \mathrm{Finset} V), D.\mathrm{card} = b \Rightarrow \mathrm{ncDamage} G D \leq b \cdot (\Delta - 1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.nc_le_budget_mul_degree_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Charge every non-root survivor component to an incident deleted vertex closer to a surviving root. Every deleted vertex also has a closer neighbor outside its available charges.

**Theorem 1.4 (Bounded degree transfers into nc).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}],\\G.\mathrm{Connected} \Rightarrow\\\forall (\Delta : \mathbb{N}),\\G.\mathrm{maxDegree} \leq \Delta \Rightarrow\\\forall b < \mathrm{Fintype}.\mathrm{card} V,\\0 < \mathrm{damageMaximum} (\mathrm{ncDamage} G) b \Rightarrow\\(\forall (D : \mathrm{Finset} V),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{pcDamage} G D = \mathrm{damageMaximum} (\mathrm{pcDamage} G) b \Rightarrow\\1 / \mathrm{coe}(b \cdot (\Delta - 1)) \leq \mathrm{damageRatio} (\mathrm{ncDamage} G) b D) \land\\\forall (D : \mathrm{Finset} V),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{lccDamage} G D = \mathrm{damageMaximum} (\mathrm{lccDamage} G) b \Rightarrow\\1 / \mathrm{coe}(b \cdot (\Delta - 1)) \leq \mathrm{damageRatio} (\mathrm{ncDamage} G) b D\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.bounded_degree_transfers_into_nc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every PC and LCC maximizer disconnects the survivors when a positive NC value is attainable. The component bound controls the common denominator.

**Definition 1.5 (Inst decidable uniform host adj).**

$$\mathrm{instDecidableUniformHostAdj} : (b k q : \mathbb{N}) \Rightarrow \mathrm{DecidableRel} (\mathrm{uniformHost} b k q).\mathrm{Adj}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.instDecidableUniformHostAdj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decide adjacency by the spine-edge test or the prescribed leaf incidence.

**Theorem 1.6 (Subcubic tree out of nc arbitrarily small).**

$$\begin{aligned}\forall (b : \mathbb{N}),\\2 \leq b \Rightarrow\\\forall (\varepsilon : \mathbb{R}),\\0 < \varepsilon \Rightarrow\\\exists q,\\2 \cdot b \cdot (1 + 2) \leq q \land\\\mathrm{let} H : = \mathrm{host} (\mathrm{uniformHub} b);\\H.\mathrm{IsTree} \land\\H.\mathrm{maxDegree} \leq 3 \land\\b < \mathrm{Fintype}.\mathrm{card} (\mathrm{UniformVertex} b 1 q) \land\\(0 < \mathrm{damageMaximum} (\mathrm{ncDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{pcDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{lccDamage} H) b) \land\\\forall (D : \mathrm{Finset} (\mathrm{UniformVertex} b 1 q)),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{ncDamage} H D = \mathrm{damageMaximum} (\mathrm{ncDamage} H) b \Rightarrow\\\mathrm{damageRatio} (\mathrm{pcDamage} H) b D < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{lccDamage} H) b D < \varepsilon\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.subcubic_tree_out_of_nc_arbitrarily_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One leaf per hub gives maximum degree at most three. Increasing the tail makes both outgoing NC comparisons small for every exact NC optimizer.

**Theorem 1.7 (Uniform tree simultaneous epsilon).**

$$\begin{aligned}\forall (b : \mathbb{N}),\\2 \leq b \Rightarrow\\\forall (\varepsilon : \mathbb{R}),\\0 < \varepsilon \Rightarrow\\\exists k q,\\1 \leq k \land\\2 \cdot b \cdot (k + 2) \leq q \land\\\mathrm{let} H : = \mathrm{host} (\mathrm{uniformHub} b);\\H.\mathrm{IsTree} \land\\b < \mathrm{Fintype}.\mathrm{card} (\mathrm{UniformVertex} b k q) \land\\(0 < \mathrm{damageMaximum} (\mathrm{ncDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{pcDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{lccDamage} H) b) \land\\\forall (\mathrm{Dn} \mathrm{Dp} \mathrm{Dl} : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\\mathrm{Dn}.\mathrm{card} = b \Rightarrow\\\mathrm{Dp}.\mathrm{card} = b \Rightarrow\\\mathrm{Dl}.\mathrm{card} = b \Rightarrow\\\mathrm{ncDamage} H \mathrm{Dn} = \mathrm{damageMaximum} (\mathrm{ncDamage} H) b \Rightarrow\\\mathrm{pcDamage} H \mathrm{Dp} = \mathrm{damageMaximum} (\mathrm{pcDamage} H) b \Rightarrow\\\mathrm{lccDamage} H \mathrm{Dl} = \mathrm{damageMaximum} (\mathrm{lccDamage} H) b \Rightarrow\\\mathrm{damageRatio} (\mathrm{ncDamage} H) b \mathrm{Dp} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{ncDamage} H) b \mathrm{Dl} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{lccDamage} H) b \mathrm{Dn} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{pcDamage} H) b \mathrm{Dn} < \varepsilon\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.uniform_tree_simultaneous_epsilon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every spine edge and leaf edge is a bridge. This certifies that the common witness for all four strict comparisons is a tree.

**Definition 1.8 (Optimistic damage ratio).**

$$\mathrm{optimisticDamageRatio} : \{V : \mathrm{Type}\} \Rightarrow [\mathrm{Fintype} V] \Rightarrow (\mathrm{Finset} V \Rightarrow \mathbb{N}) \Rightarrow (\mathrm{Finset} V \Rightarrow \mathbb{N}) \Rightarrow \mathbb{N} \Rightarrow \mathbb{R}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.optimisticDamageRatio` (`✓ std3`).

*Citation.* Onur Uğurlu (2026). *Objective Transfer in Single-Node Network Criticality: Optimal Constants and Exact Separation Thresholds*. DOI: [10.48550/arXiv.2609.34394](https://doi.org/10.48550/arXiv.2609.34394). URL: <https://arxiv.org/abs/2609.34394v1>.

*Commentary.*

Section 2 resolves source ties by maximizing the attained target score over the exact source optimizers. The denominator is the exact target maximum.

**Theorem 1.9 (Optimistic ratio eq one of common).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{Fintype} V] (\mathrm{source} \mathrm{target} : \mathrm{Finset} V \Rightarrow \mathbb{N}) (b : \mathbb{N}) (D : \mathrm{Finset} V),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{source} D = \mathrm{damageMaximum} \mathrm{source} b \Rightarrow\\\mathrm{target} D = \mathrm{damageMaximum} \mathrm{target} b \Rightarrow\\0 < \mathrm{damageMaximum} \mathrm{target} b \Rightarrow \mathrm{optimisticDamageRatio} \mathrm{source} \mathrm{target} b = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.optimistic_ratio_eq_one_of_common` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source optimizer that also attains the target maximum makes that value attainable in the optimistic numerator.

**Definition 1.10 (Subcubic tree optimistic out of nc).**

$$\mathrm{subcubicTreeOptimisticOutOfNC} : \mathbb{N} \Rightarrow \mathrm{Bool} \Rightarrow \mathrm{Set} \mathbb{R}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.subcubicTreeOptimisticOutOfNC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean selects PC when true and LCC when false. The set uses finite trees of maximum degree at most three and requires positivity for the selected target.

**Theorem 1.11 (Subcubic tree optimistic out of nc infimum zero).**

$$\forall (b : \mathbb{N}), 2 \leq b \Rightarrow \forall (\mathrm{pc} : \mathrm{Bool}), \mathrm{sInf} (\mathrm{subcubicTreeOptimisticOutOfNC} b \mathrm{pc}) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.subcubic_tree_optimistic_out_of_nc_infimum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All ratios are nonnegative. The one-leaf trees give a member below every positive threshold.

**Theorem 1.12 (Common optimizer of balanced maximal profile).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}]\\(b m q : \mathbb{N}) (D : \mathrm{Finset} V),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{Fintype}.\mathrm{card} (\mathrm{survivorGraph} G D).\mathrm{ConnectedComponent} = m \Rightarrow\\0 < m \Rightarrow\\(\forall (C : (\mathrm{survivorGraph} G D).\mathrm{ConnectedComponent}),\\C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card} = q \lor C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card} = q + 1) \Rightarrow\\(\forall (E : \mathrm{Finset} V), E.\mathrm{card} = b \Rightarrow \mathrm{Fintype}.\mathrm{card} (\mathrm{survivorGraph} G E).\mathrm{ConnectedComponent} \leq m) \Rightarrow\\\mathrm{ncDamage} G D = \mathrm{damageMaximum} (\mathrm{ncDamage} G) b \land\\\mathrm{pcDamage} G D = \mathrm{damageMaximum} (\mathrm{pcDamage} G) b \land\\\mathrm{lccDamage} G D = \mathrm{damageMaximum} (\mathrm{lccDamage} G) b\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.common_optimizer_of_balanced_maximal_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximal feasible number of runs and sizes differing by at most one simultaneously bound the largest part and minimize the sum of within-component pairs.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.bounded_degree_transfers_into_nc`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.common_optimizer_of_balanced_maximal_profile`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.component_card_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.instDecidableUniformHostAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.nc_le_budget_mul_degree_sub_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.optimisticDamageRatio`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.optimistic_ratio_eq_one_of_common`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.subcubicTreeOptimisticOutOfNC`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.subcubic_tree_optimistic_out_of_nc_infimum_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.subcubic_tree_out_of_nc_arbitrarily_small`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.survivor_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.uniform_tree_simultaneous_epsilon`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Coloring](../Brooks/Coloring.md)
- Dependency: [D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer](TreeTransfer.md)
