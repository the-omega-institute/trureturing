# Exact optimizers on the tree with pendant leaves

## Abstract

Exact hub and balanced optimizers yield four small transfer ratios.

**Definition 1.1 (Host hub).**

$$\mathrm{hostHub} : \{p t b k : \mathbb{N}\} \Rightarrow (\mathrm{Fin} b \Rightarrow \mathrm{Fin} p) \Rightarrow \mathrm{Fin} b \Rightarrow \mathrm{Vertex} p t b k$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.hostHub` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Include the specified hub in the spine summand of the host carrier.

**Theorem 1.2 (Component eq iff of no adj).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} \{G : \mathrm{SimpleGraph} V\} \{v : V\},\\(\forall (w : V), \neg G.\mathrm{Adj} v w) \Rightarrow \forall (w : V), G.\mathrm{connectedComponentMk} v = G.\mathrm{connectedComponentMk} w \iff v = w\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.component_eq_iff_of_no_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct reachable vertices have incident edges, so the component of an isolated vertex is a singleton.

**Theorem 1.3 (Uniform hub deletion unique nc optimizer).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\1 \leq k \Rightarrow\\2 \cdot b \cdot (k + 2) \leq q \Rightarrow\\\forall (D : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\D.\mathrm{card} = b \Rightarrow\\\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b)) D \leq\\\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))\\(\mathrm{uniformHubDeletion} b k q) \land\\(\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b)) D =\\\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))\\(\mathrm{uniformHubDeletion} b k q) \iff\\D = \mathrm{uniformHubDeletion} b k q)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_hub_deletion_unique_nc_optimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each deleted hub can detach its k leaves. Equality in the component bound requires every deletion to be a hub.

**Theorem 1.4 (Uniform order).**

$$\forall \{b k q : \mathbb{N}\}, 2 \cdot b \cdot (k + 2) \leq q \Rightarrow \mathrm{Fintype}.\mathrm{card} (\mathrm{UniformVertex} b k q) = (b + 1) \cdot q + b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Add the exact deletion budget to the survivor count.

**Theorem 1.5 (Damage maximum eq of dominates).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{DecidableEq} V] [\mathrm{Fintype} V] (\mathrm{score} : \mathrm{Finset} V \Rightarrow \mathbb{N}) (b : \mathbb{N}) (D : \mathrm{Finset} V),\\D.\mathrm{card} = b \Rightarrow (\forall (E : \mathrm{Finset} V), E.\mathrm{card} = b \Rightarrow \mathrm{score} E \leq \mathrm{score} D) \Rightarrow \mathrm{damageMaximum} \mathrm{score} b = \mathrm{score} D\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.damageMaximum_eq_of_dominates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An attained pointwise maximum is the supremum over the exact-budget cuts.

**Theorem 1.6 (Uniform exact budget maxima).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\1 \leq k \Rightarrow\\\forall (\mathrm{hq} : 2 \cdot b \cdot (k + 2) \leq q),\\(\mathrm{damageMaximum} (\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b =\\\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))\\(\mathrm{uniformHubDeletion} b k q) \land\\\mathrm{damageMaximum} (\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b =\\\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b))\\(\mathrm{uniformBalancedDeletion} \mathrm{hq}) \land\\\mathrm{damageMaximum} (\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b =\\\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b))\\(\mathrm{uniformBalancedDeletion} \mathrm{hq})) \land\\(\mathrm{damageMaximum} (\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b =\\b \cdot (k + 1) \land\\\mathrm{damageMaximum} (\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b =\\((b + 1) \cdot q + b).\mathrm{choose} 2 - (b + 1) \cdot q.\mathrm{choose} 2 \land\\\mathrm{damageMaximum} (\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b =\\b \cdot (q + 1)) \land\\0 < \mathrm{damageMaximum} (\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b \land\\0 < \mathrm{damageMaximum} (\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b \land\\0 < \mathrm{damageMaximum} (\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_exact_budget_maxima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the unique hub optimizer for NC and the unique balanced optimizer for both other scores.

**Definition 1.7 (Damage ratio).**

$$\begin{aligned}\forall \{V : \mathrm{Type}\} [\mathrm{Fintype} V] (\mathrm{target} : \mathrm{Finset} V \Rightarrow \mathbb{N}) (b : \mathbb{N}) (D : \mathrm{Finset} V), \mathrm{damageRatio} \mathrm{target} b D =\\(\mathrm{coe}(\mathrm{target} D) : \mathbb{R}) / \mathrm{coe}(\mathrm{damageMaximum} \mathrm{target} b)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.damageRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value at this deletion is divided by the exact-budget maximum for the target score. The classification imposes a positive target maximum.

**Theorem 1.8 (Uniform transfer identities).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\1 \leq k \Rightarrow\\2 \cdot b \cdot (k + 2) \leq q \Rightarrow\\\forall (\mathrm{Dn} \mathrm{Dp} \mathrm{Dl} : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\\mathrm{Dn}.\mathrm{card} = b \Rightarrow\\\mathrm{Dp}.\mathrm{card} = b \Rightarrow\\\mathrm{Dl}.\mathrm{card} = b \Rightarrow\\\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b)) \mathrm{Dn} =\\\mathrm{damageMaximum} (\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b \Rightarrow\\\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b)) \mathrm{Dp} =\\\mathrm{damageMaximum} (\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b \Rightarrow\\\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b)) \mathrm{Dl} =\\\mathrm{damageMaximum} (\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b)))\\b \Rightarrow\\\mathrm{damageRatio} (\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b\\\mathrm{Dp} =\\1 / (\mathrm{coe}k + 1) \land\\\mathrm{damageRatio} (\mathrm{ncDamage} (\mathrm{host} (\mathrm{uniformHub} b))) b\\\mathrm{Dl} =\\1 / (\mathrm{coe}k + 1) \land\\\mathrm{damageRatio} (\mathrm{lccDamage} (\mathrm{host} (\mathrm{uniformHub} b)))\\b \mathrm{Dn} =\\\mathrm{coe}(b \cdot (k + 2)) / \mathrm{coe}(b \cdot (q + 1)) \land\\\mathrm{damageRatio} (\mathrm{pcDamage} (\mathrm{host} (\mathrm{uniformHub} b)))\\b \mathrm{Dn} =\\\mathrm{coe}(((b + 1) \cdot q + b).\mathrm{choose} 2 - (\mathrm{uniformTailLength} b k q).\mathrm{choose} 2) /\\\mathrm{coe}(((b + 1) \cdot q + b).\mathrm{choose} 2 - (b + 1) \cdot q.\mathrm{choose} 2)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_transfer_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Optimizer uniqueness fixes the denominator and the source cut in each of the four evaluations.

**Theorem 1.9 (Uniform pc transfer bound).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\},\\2 \leq b \Rightarrow\\2 \cdot b \cdot (k + 2) \leq q \Rightarrow\\\mathrm{coe}(((b + 1) \cdot q + b).\mathrm{choose} 2 - (\mathrm{uniformTailLength} b k q).\mathrm{choose} 2) /\\\mathrm{coe}(((b + 1) \cdot q + b).\mathrm{choose} 2 - (b + 1) \cdot q.\mathrm{choose} 2) \leq\\\mathrm{coe}(4 \cdot (b \cdot (k + 2))) / \mathrm{coe}(b \cdot q)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_pc_transfer_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare the PC damage from the hub cut with the positive balanced optimum.

**Theorem 1.10 (Uniform lcc transfer bound).**

$$\begin{aligned}\forall \{b k q : \mathbb{N}\}, 2 \leq b \Rightarrow 2 \cdot b \cdot (k + 2) \leq q \Rightarrow \mathrm{coe}(b \cdot (k + 2)) / \mathrm{coe}(b \cdot (q + 1)) \leq \mathrm{coe}(4 \cdot (b \cdot (k + 2)))\\/ \mathrm{coe}(b \cdot q)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_lcc_transfer_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare the largest survivor under the hub cut with the balanced target optimum.

**Theorem 1.11 (Uniform simultaneous epsilon).**

$$\begin{aligned}\forall (b : \mathbb{N}),\\2 \leq b \Rightarrow\\\forall (\varepsilon : \mathbb{R}),\\0 < \varepsilon \Rightarrow\\\exists k q,\\1 \leq k \land\\2 \cdot b \cdot (k + 2) \leq q \land\\\mathrm{let} H : = \mathrm{host} (\mathrm{uniformHub} b);\\(0 < \mathrm{damageMaximum} (\mathrm{ncDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{pcDamage} H) b \land\\0 < \mathrm{damageMaximum} (\mathrm{lccDamage} H) b) \land\\\forall (\mathrm{Dn} \mathrm{Dp} \mathrm{Dl} : \mathrm{Finset} (\mathrm{UniformVertex} b k q)),\\\mathrm{Dn}.\mathrm{card} = b \Rightarrow\\\mathrm{Dp}.\mathrm{card} = b \Rightarrow\\\mathrm{Dl}.\mathrm{card} = b \Rightarrow\\\mathrm{ncDamage} H \mathrm{Dn} = \mathrm{damageMaximum} (\mathrm{ncDamage} H) b \Rightarrow\\\mathrm{pcDamage} H \mathrm{Dp} = \mathrm{damageMaximum} (\mathrm{pcDamage} H) b \Rightarrow\\\mathrm{lccDamage} H \mathrm{Dl} = \mathrm{damageMaximum} (\mathrm{lccDamage} H) b \Rightarrow\\\mathrm{damageRatio} (\mathrm{ncDamage} H) b \mathrm{Dp} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{ncDamage} H) b \mathrm{Dl} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{lccDamage} H) b \mathrm{Dn} < \varepsilon \land\\\mathrm{damageRatio} (\mathrm{pcDamage} H) b \mathrm{Dn} < \varepsilon\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_simultaneous_epsilon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose k for the two inbound comparisons and then q for the two outgoing comparisons on the same host.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.component_eq_iff_of_no_adj`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.damageMaximum_eq_of_dominates`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.damageRatio`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.hostHub`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_exact_budget_maxima`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_hub_deletion_unique_nc_optimizer`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_lcc_transfer_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_order`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_pc_transfer_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_simultaneous_epsilon`
- Truth anchor: `D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.uniform_transfer_identities`
- Dependency: [D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts](BalancedCuts.md)
