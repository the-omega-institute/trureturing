# Induced survivor components and tail runs

## Abstract

Actual tail runs and induced survivor scores for exact vertex cuts.

**Definition 1.1 (Vertex).**

$$\forall (p t b k : \mathbb{N}), \mathrm{Vertex} p t b k = \mathrm{Fin} (p + t) \mathrm{Sum} (\mathrm{Fin} b \times \mathrm{Fin} k)$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use a disjoint sum of spine positions and the pairs of hub and leaf indices.

**Definition 1.2 (Host).**

$$\mathrm{host} : \{p t b k : \mathbb{N}\} \Rightarrow (\mathrm{Fin} b \Rightarrow \mathrm{Fin} p) \Rightarrow \mathrm{SimpleGraph} (\mathrm{Vertex} p t b k)$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.host` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spine edges form a path and every leaf is adjacent to its indexed hub.

**Definition 1.3 (Position).**

$$\mathrm{position} : \{p t b k : \mathbb{N}\} \Rightarrow (\mathrm{Fin} b \Rightarrow \mathrm{Fin} p) \Rightarrow \mathrm{Vertex} p t b k \Rightarrow \mathbb{N}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Project a spine vertex to its index and a leaf to its hub index.

**Definition 1.4 (Tail vertex).**

$$\mathrm{tailVertex} : \{p t b k : \mathbb{N}\} \Rightarrow \mathrm{Fin} t \Rightarrow \mathrm{Vertex} p t b k$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tailVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Insert the tail index after all p prefix positions.

**Definition 1.5 (Survivors).**

$$\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] (D : \mathrm{Finset} V), \mathrm{survivors} D = \{v : V \mid v \neg\in D\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier contains precisely the vertices outside the deletion finset.

**Definition 1.6 (Survivor graph).**

$$\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] (G : \mathrm{SimpleGraph} V) (D : \mathrm{Finset} V), \mathrm{survivorGraph} G D = G.\mathrm{induce} (\mathrm{survivors} D)$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivorGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjacency relation is induced by the original graph on the surviving carrier.

**Theorem 1.7 (Host adj position).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (u v : \mathrm{Vertex} p t b k),\\(\mathrm{host} \mathrm{hub}).\mathrm{Adj} u v \Rightarrow\\\mathrm{position} \mathrm{hub} u = \mathrm{position} \mathrm{hub} v \lor\\\mathrm{position} \mathrm{hub} u + 1 = \mathrm{position} \mathrm{hub} v \lor\\\mathrm{position} \mathrm{hub} v + 1 = \mathrm{position} \mathrm{hub} u\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.host_adj_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge preserves the spine coordinate or changes it by one.

**Definition 1.8 (Surviving tail vertex).**

$$\begin{aligned}\mathrm{survivingTailVertex} : \{p t b k : \mathbb{N}\} \Rightarrow\\(D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) \Rightarrow (i : \mathrm{Fin} t) \Rightarrow \mathrm{tailVertex} i \neg\in D \Rightarrow \mathrm{coe}(\mathrm{survivors} D)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the given survival proof to enter the induced graph carrier.

**Theorem 1.9 (Tail interval reachable).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) \{x y : \mathrm{Fin} t\}\\(\mathrm{hx} : \mathrm{tailVertex} x \neg\in D) (\mathrm{hy} : \mathrm{tailVertex} y \neg\in D),\\\mathrm{coe}x \leq \mathrm{coe}y \Rightarrow\\(\forall (z : \mathrm{Fin} t), \mathrm{coe}x \leq \mathrm{coe}z \Rightarrow \mathrm{coe}z \leq \mathrm{coe}y \Rightarrow \mathrm{tailVertex} z \neg\in D) \Rightarrow\\(\mathrm{survivorGraph} (\mathrm{host} \mathrm{hub}) D).\mathrm{Reachable} (\mathrm{survivingTailVertex} D x \mathrm{hx})\\(\mathrm{survivingTailVertex} D y \mathrm{hy})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tail_interval_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consecutive surviving tail positions form an induced path through the interval.

**Theorem 1.10 (Tail component eq iff).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) \{x y : \mathrm{Fin} t\}\\(\mathrm{hx} : \mathrm{tailVertex} x \neg\in D) (\mathrm{hy} : \mathrm{tailVertex} y \neg\in D),\\\mathrm{coe}x \leq \mathrm{coe}y \Rightarrow\\((\mathrm{survivorGraph} (\mathrm{host} \mathrm{hub}) D).\mathrm{connectedComponentMk}\\(\mathrm{survivingTailVertex} D x \mathrm{hx}) =\\(\mathrm{survivorGraph} (\mathrm{host} \mathrm{hub}) D).\mathrm{connectedComponentMk}\\(\mathrm{survivingTailVertex} D y \mathrm{hy}) \iff\\\forall (z : \mathrm{Fin} t), \mathrm{coe}x \leq \mathrm{coe}z \Rightarrow \mathrm{coe}z \leq \mathrm{coe}y \Rightarrow \mathrm{tailVertex} z \neg\in D)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tail_component_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A gap separates the two endpoints, and a fully surviving interval connects them.

**Definition 1.11 (Tail run component).**

$$\begin{aligned}\mathrm{TailRun}.\mathrm{component} : \{p t b k : \mathbb{N}\} \Rightarrow\\(\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) \Rightarrow\\(D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) \Rightarrow\\\mathrm{TailRun} D \Rightarrow (\mathrm{survivorGraph} (\mathrm{host} \mathrm{hub}) D).\mathrm{ConnectedComponent}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.component` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the actual induced graph component of the first vertex in the run.

**Theorem 1.12 (Tail run component eq).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) (r : \mathrm{TailRun} D) (z : \mathrm{Fin} t)\\(\mathrm{hl} : \mathrm{coe}r.\mathrm{first} \leq \mathrm{coe}z) (\mathrm{hr} : \mathrm{coe}z \leq \mathrm{coe}r.\mathrm{last}),\\\mathrm{TailRun}.\mathrm{component} \mathrm{hub} D r =\\(\mathrm{survivorGraph} (\mathrm{host} \mathrm{hub}) D).\mathrm{connectedComponentMk} (\mathrm{survivingTailVertex} D z proof)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.component_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every tail vertex of the run lies in the component of its first vertex.

**Theorem 1.13 (Tail run component injective).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)),\\\mathrm{Function}.\mathrm{Injective} (\mathrm{TailRun}.\mathrm{component} \mathrm{hub} D)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tail_run_component_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Between distinct positive surviving tail runs there is a deleted spine position which no projected survivor walk can cross.

**Definition 1.14 (Uniform hub).**

$$\forall (b : \mathbb{N}) (i : \mathrm{Fin} b), \mathrm{coe}(\mathrm{uniformHub} b i) = 2 \cdot \mathrm{coe}i + 1$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniformHub` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the odd spine indices among the first 2b positions.

**Theorem 1.15 (Uniform hubs independent).**

$$\begin{aligned}\forall (b : \mathbb{N}),\\\mathrm{Function}.\mathrm{Injective} (\mathrm{uniformHub} b) \land\\\forall (i j : \mathrm{Fin} b), \neg(\mathrm{SimpleGraph}.\mathrm{pathGraph} (2 \cdot b)).\mathrm{Adj} (\mathrm{uniformHub} b i) (\mathrm{uniformHub} b j)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_hubs_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct odd positions are distinct vertices and cannot be consecutive.

**Definition 1.16 (Uniform tail length).**

$$\forall (b k q : \mathbb{N}), \mathrm{uniformTailLength} b k q = (b + 1) \cdot q + b - b \cdot (k + 2)$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniformTailLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set the tail length so that b+1 parts of size q remain after deleting b vertices.

**Definition 1.17 (Uniform vertex).**

$$\forall (b k q : \mathbb{N}), \mathrm{UniformVertex} b k q = \mathrm{Vertex} (2 \cdot b) (\mathrm{uniformTailLength} b k q) b k$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.UniformVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the tail length and the prefix of length 2b from the uniform host construction.

**Definition 1.18 (Uniform host).**

$$\forall (b k q : \mathbb{N}), \mathrm{uniformHost} b k q = \mathrm{host} (\mathrm{uniformHub} b)$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniformHost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Place k leaves at every odd prefix position.

**Theorem 1.19 (Uniform survivor card).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \cdot b \cdot (k + 2) \leq q \Rightarrow \forall (D : \mathrm{Finset} (\mathrm{UniformVertex} b k q)), D.\mathrm{card} = b \Rightarrow D^{c}.\mathrm{card} = (b + 1) \cdot q\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_survivor_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract b from the total number of spine and leaf vertices.

**Definition 1.20 (Inst fintype survivors).**

$$\begin{aligned}\mathrm{instFintypeSurvivors} : \{V : \mathrm{Type}\} \Rightarrow [\mathrm{DecidableEq} V] \Rightarrow [\mathrm{Fintype} V] \Rightarrow (D : \mathrm{Finset} V) \Rightarrow\\\mathrm{Fintype} \mathrm{coe}(\mathrm{survivors} D)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.instFintypeSurvivors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Enumerate the finite complement of the deletion.

**Definition 1.21 (Inst decidable survivor adj).**

$$\begin{aligned}\mathrm{instDecidableSurvivorAdj} : \{V : \mathrm{Type}\} \Rightarrow\\{}[\mathrm{DecidableEq} V] \Rightarrow\\(G : \mathrm{SimpleGraph} V) \Rightarrow (D : \mathrm{Finset} V) \Rightarrow [\mathrm{DecidableRel} G.\mathrm{Adj}] \Rightarrow \mathrm{DecidableRel} (\mathrm{survivorGraph} G D).\mathrm{Adj}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.instDecidableSurvivorAdj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the original adjacency decision to the surviving carrier.

**Definition 1.22 (Component sizes).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}] (D : \mathrm{Finset} V),\\\mathrm{componentSizes} G D = \mathrm{Finset}.\mathrm{univ}.\mathrm{val}.\mathrm{map} (\lambda C : (\mathrm{survivorGraph} G D).\mathrm{ConnectedComponent} \mapsto\\C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.componentSizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the multiset of sizes of the actual connected components of the induced survivor graph. Repeated sizes are counted with multiplicity.

**Definition 1.23 (Nc damage).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}] (D : \mathrm{Finset} V),\\\mathrm{ncDamage} G D = (\mathrm{componentSizes} G D).\mathrm{card} - 1\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.ncDamage` (`✓ std3`).

*Citation.* Onur Uğurlu (2026). *Objective Transfer in Single-Node Network Criticality: Optimal Constants and Exact Separation Thresholds*. DOI: [10.48550/arXiv.2609.34394](https://doi.org/10.48550/arXiv.2609.34394). URL: <https://arxiv.org/abs/2609.34394v1>.

*Commentary.*

Section 2 defines component-count damage as the increase in the number of components. For a connected host the original count is one, and the natural-number subtraction truncates at zero.

**Definition 1.24 (Pc damage).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}] (D : \mathrm{Finset} V),\\\mathrm{pcDamage} G D = (\mathrm{Fintype}.\mathrm{card} V).\mathrm{choose} 2 - ((\mathrm{componentSizes} G D).\mathrm{map} (\lambda c : \mathbb{N} \mapsto c.\mathrm{choose} 2)).\mathrm{sum}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.pcDamage` (`✓ std3`).

*Citation.* Onur Uğurlu (2026). *Objective Transfer in Single-Node Network Criticality: Optimal Constants and Exact Separation Thresholds*. DOI: [10.48550/arXiv.2609.34394](https://doi.org/10.48550/arXiv.2609.34394). URL: <https://arxiv.org/abs/2609.34394v1>.

*Commentary.*

Section 2 counts all original pairs and subtracts the pairs within each surviving component. Deleted vertices are included in the damage.

**Definition 1.25 (Lcc damage).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}] (D : \mathrm{Finset} V),\\\mathrm{lccDamage} G D = \mathrm{Fintype}.\mathrm{card} V - (\mathrm{componentSizes} G D).\mathrm{sup}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.lccDamage` (`✓ std3`).

*Citation.* Onur Uğurlu (2026). *Objective Transfer in Single-Node Network Criticality: Optimal Constants and Exact Separation Thresholds*. DOI: [10.48550/arXiv.2609.34394](https://doi.org/10.48550/arXiv.2609.34394). URL: <https://arxiv.org/abs/2609.34394v1>.

*Commentary.*

Section 2 subtracts the largest surviving component size from the original order.

**Definition 1.26 (Damage maximum).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{Fintype} V] (\mathrm{score} : \mathrm{Finset} V \Rightarrow \mathbb{N}) (b : \mathbb{N}), \mathrm{damageMaximum} \mathrm{score} b = ((\mathrm{Finset}.\mathrm{univ} :\\\mathrm{Finset} V).\mathrm{powersetCard} b).\mathrm{sup} \mathrm{score}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.damageMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum is taken over the finset of subsets with cardinality exactly the budget.

**Definition 1.27 (Inst decidable rel vertex adj host).**

$$\begin{aligned}\mathrm{instDecidableRelVertexAdjHost} : \{p t b k : \mathbb{N}\} \Rightarrow (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) \Rightarrow \mathrm{DecidableRel}\\(\mathrm{host} \mathrm{hub}).\mathrm{Adj}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.instDecidableRelVertexAdjHost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decide spine adjacency or check whether the spine vertex is the specified hub.

**Definition 1.28 (Deleted tail indices).**

$$\mathrm{deletedTailIndices} : \{p t b k : \mathbb{N}\} \Rightarrow \mathrm{Finset} (\mathrm{Vertex} p t b k) \Rightarrow \mathrm{Finset} (\mathrm{Fin} t)$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.deletedTailIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the tail positions by whether their vertices are deleted.

**Definition 1.29 (Surviving tail vertices).**

$$\begin{aligned}\mathrm{survivingTailVertices} : \{p t b k : \mathbb{N}\} \Rightarrow (\mathrm{Fin} b \Rightarrow \mathrm{Fin} p) \Rightarrow (D : \mathrm{Finset} (\mathrm{Vertex} p t b k))\\\Rightarrow \mathrm{Finset} \mathrm{coe}(\mathrm{survivors} D)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select the survivors whose spine coordinates lie in the tail.

**Definition 1.30 (Positive tail components).**

$$\begin{aligned}\mathrm{positiveTailComponents} : \{p t b k : \mathbb{N}\} \Rightarrow\\(\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) \Rightarrow\\(D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) \Rightarrow\\\mathrm{Finset} (\mathrm{survivorGraph} (\mathrm{host} \mathrm{hub}) D).\mathrm{ConnectedComponent}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.positiveTailComponents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the image of the surviving tail vertices under the actual component map.

**Theorem 1.31 (Mem deleted tail indices).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) (i : \mathrm{Fin} t),\\i \in \mathrm{deletedTailIndices} D \iff \mathrm{tailVertex} i \in D\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.mem_deletedTailIndices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership is exactly deletion of the associated tail vertex.

**Theorem 1.32 (Surviving tail vertex mem).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) (i : \mathrm{Fin} t)\\(\mathrm{hi} : \mathrm{tailVertex} i \neg\in D), \mathrm{survivingTailVertex} D i \mathrm{hi} \in \mathrm{survivingTailVertices} \mathrm{hub} D\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertex_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every surviving tail index gives a vertex in this finset.

**Theorem 1.33 (Exists surviving tail vertex).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) \{v : \mathrm{coe}(\mathrm{survivors} D)\},\\v \in \mathrm{survivingTailVertices} \mathrm{hub} D \Rightarrow\\\exists i, \exists (\mathrm{hi} : \mathrm{tailVertex} i \neg\in D), \mathrm{survivingTailVertex} D i \mathrm{hi} = v\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.exists_survivingTailVertex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vertex in this finset has a surviving tail index.

**Theorem 1.34 (Surviving tail vertices card).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)),\\(\mathrm{survivingTailVertices} \mathrm{hub} D).\mathrm{card} = t - (\mathrm{deletedTailIndices} D).\mathrm{card}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertices_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The surviving tail indices are in bijection with the surviving tail vertices.

**Theorem 1.35 (Positive tail component has run).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (\mathrm{hub} : \mathrm{Fin} b \Rightarrow \mathrm{Fin} p) (D : \mathrm{Finset} (\mathrm{Vertex} p t b k))\\\{C : (\mathrm{survivorGraph} (\mathrm{host} \mathrm{hub}) D).\mathrm{ConnectedComponent}\},\\C \in \mathrm{positiveTailComponents} \mathrm{hub} D \Rightarrow \exists r, \mathrm{TailRun}.\mathrm{component} \mathrm{hub} D r = C\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.positiveTailComponent_has_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the maximal surviving interval through a tail vertex in the component.

**Definition 1.36 (Tail run predecessor or first).**

$$\begin{aligned}\mathrm{TailRun}.\mathrm{predecessorOrFirst} : \{p t b k : \mathbb{N}\} \Rightarrow\\(D : \mathrm{Finset} (\mathrm{Vertex} p t b k)) \Rightarrow \mathrm{TailRun} D \Rightarrow \mathrm{Option} \mathrm{Subtype}(\mathrm{deletedTailIndices} D)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.predecessorOrFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use no predecessor for an initial run and otherwise record its deleted predecessor.

**Theorem 1.37 (Tail run predecessor or first injective).**

$$\begin{aligned}\forall \{p t b k : \mathbb{N}\} (D : \mathrm{Finset} (\mathrm{Vertex} p t b k)), \mathrm{Function}.\mathrm{Injective}\\(\mathrm{TailRun}.\mathrm{predecessorOrFirst} D)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.predecessorOrFirst_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The predecessor determines the first vertex, and maximality determines the last vertex.

**Theorem 1.38 (Uniform tail component count and mass).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\1 \leq k \Rightarrow\\2 \cdot b \cdot (k + 2) \leq q \Rightarrow\\\forall (D : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{let} t : = \mathrm{uniformTailLength} b k q;\\\mathrm{let} G : = \mathrm{survivorGraph} (\mathrm{uniformHost} b k q) D;\\\mathrm{have} I : = \{i \mid \mathrm{tailVertex} i \in D\};\\\mathrm{have} A : = \{v \mid 2 \cdot b \leq \mathrm{position} (\mathrm{uniformHub} b) \mathrm{coe}v\};\\\mathrm{have} J : = \mathrm{Finset}.\mathrm{image} G.\mathrm{connectedComponentMk} A;\\\mathrm{have} w : = \lambda C \mapsto \{v \in A \mid G.\mathrm{connectedComponentMk} v = C\}.\mathrm{card};\\J.\mathrm{card} \leq I.\mathrm{card} + 1 \land \sum C \in J, w C = t - I.\mathrm{card} \land \forall C \in J, w C \leq C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_tail_component_count_and_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Charge the start of each positive tail run to its deleted predecessor or the initial position. Summing the tail mass counts each surviving tail vertex once.

**Theorem 1.39 (Sum component card).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (G : \mathrm{SimpleGraph} V) [\mathrm{DecidableRel} G.\mathrm{Adj}],\\\sum C, C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card} = \mathrm{Fintype}.\mathrm{card} V\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.sum_component_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition the carrier by its actual component and sum the corresponding fiber sizes.

**Theorem 1.40 (Twice choose two add).**

$$\forall (n : \mathbb{N}), 2 \cdot n.\mathrm{choose} 2 + n = n ^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.twice_choose_two_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrite the binomial coefficient with its explicit formula and simplify.

**Theorem 1.41 (Uniform fewer tail components strict score comparisons).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\1 \leq k \Rightarrow\\2 \cdot b \cdot (k + 2) \leq q \Rightarrow\\\forall (D : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\D.\mathrm{card} = b \Rightarrow\\(\mathrm{positiveTailComponents} (\mathrm{uniformHub} b) D).\mathrm{card} \leq b \Rightarrow\\\mathrm{let} G : = \mathrm{survivorGraph} (\mathrm{uniformHost} b k q) D;\\\mathrm{have} n : = \mathrm{Fintype}.\mathrm{card} (\mathrm{UniformVertex} b k q);\\(b + 1) \cdot q.\mathrm{choose} 2 < \sum C, C.\mathrm{supp}.\mathrm{toFinset}.\mathrm{card}.\mathrm{choose} 2 \land\\\mathrm{pcDamage} (\mathrm{uniformHost} b k q) D < n.\mathrm{choose} 2 - (b + 1) \cdot q.\mathrm{choose} 2 \land\\\mathrm{lccDamage} (\mathrm{uniformHost} b k q) D < n - q\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_fewer_tail_components_strict_score_comparisons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the tail mass lies in at most b components, its total and the sum-of-squares bound force a larger maximum part and more within-component pairs than the balanced profile.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.UniformVertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.component`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.componentSizes`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.component_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.damageMaximum`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.deletedTailIndices`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.exists_survivingTailVertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.host`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.host_adj_position`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.instDecidableRelVertexAdjHost`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.instDecidableSurvivorAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.instFintypeSurvivors`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.lccDamage`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.mem_deletedTailIndices`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.ncDamage`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.pcDamage`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.position`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.positiveTailComponent_has_run`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.positiveTailComponents`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.predecessorOrFirst`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.predecessorOrFirst_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.sum_component_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertex_mem`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivingTailVertices_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivorGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.survivors`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tailVertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tail_component_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tail_interval_reachable`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.tail_run_component_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.twice_choose_two_add`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniformHost`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniformHub`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniformTailLength`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_fewer_tail_components_strict_score_comparisons`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_hubs_independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_survivor_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.uniform_tail_component_count_and_mass`
