---
slug: cambie-jooken-wagner-mean-order-comparison
bibkey: cambiejookenwagner2026meansubtrees
doi: 10.48550/arXiv.2508.20593
url: https://arxiv.org/abs/2508.20593v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.result
---

# Mean subtree order can be smaller than mean connected-set order

## Problem

Stijn Cambie, Jorik Jooken and Stephan Wagner ask in *On the extrema of the mean subtree order of graphs*, arXiv:2508.20593v2, Question 1.9.

> Is it true that μ(G) ≥ av(G) holds for every connected graph G?

Here $G$ is a finite simple connected graph. The subtree mean $\mu(G)$ counts each actual tree subgraph, distinguishing different edge sets on the same vertices. The connected-set mean $\operatorname{av}(G)$ counts each connected induced vertex support once. Both means give weight to singletons. [Question 1.9 and Section 2](https://arxiv.org/pdf/2508.20593v2#page=3)

## Motivation

The two averages differ in their weights on the same supports. A tree has one tree on each connected support. The paper observes that the proposed comparison, together with the known lower bound for the connected-set mean, would give an alternative route to the path minimum. [Introduction](https://arxiv.org/pdf/2508.20593v2#page=3)

## Gap

A graph can give a large extra weight to a support that contains a full cycle. Establishing the resulting change in the mean requires the actual tree multiplicities on every connected support. In partial cycle restrictions that induce a path, every edge is forced.

## Route

Take a cycle of order 5,000, attach two paths of 500 new vertices at cycle positions 0 and 1,000, and join a triangle by a bridge at position 500. The three joins meet vertex 0 of their attached blocks. The host has 6,003 vertices.

Classify the connected induced supports as a cyclic interval with permitted path prefixes and a triangle subset, or a support contained entirely in a single attached block. A full cyclic interval is a separate case. For each configuration, classify the actual trees as choices of one edge from each fully included cycle to delete. A proper restriction contributes a unique no-deletion choice. The inverse trees keep exactly the other induced edges.

The support and tree equivalences preserve vertex order pointwise. Write $k(c)$ for the order of a configuration and $m(c)$ for the product of its core and triangle multiplicities. A full core contributes 5,000 and a full triangle contributes 3. A proper restriction contributes 1. The two connected-set moments are $\sum_c 1$ and $\sum_c k(c)$, while the two tree moments are $\sum_c m(c)$ and $\sum_c k(c)m(c)$. The tree transport preserves the original sum by order \(1\) through the host cardinality.

## Falsifier

The universal inequality is false on this host. The connected-set mean exceeds the tree mean by exactly
$$
\frac{1769250196421378505239933}{18998398362554330511481326} > 0.
$$

## Evidence

| Objects | Count | Sum of vertex orders |
| --- | ---: | ---: |
| Connected induced supports | 10,425,438,990,512 | 43,855,001,336,852,520 |
| Actual tree subgraphs | 14,578,492,765,509 | 61,323,620,645,707,018 |

The Lean proposition is the closed universal comparison, with exact rational division and the Mathlib connectedness guard. The designated result has literal type `Not claim`. Its two moment branches use the support equivalence and the dependent tree-fiber equivalence.

Cambie, Jooken and Wagner posed the question and defined the means. Loning (`loning`) authored experiment commit `6ef92106b2636a4c2e3a926bb6ce384abb1fdf8a`. ElonSG pushed that commit and opened issue #31895 with the construction, counting argument and exact gap. The prospective comment by `macstudio-2[bot]` specified the actual support and tree-fiber equivalences and their pointwise order laws. The original Codex CLI implementation produced those Lean proofs and the exact refutation under the recorded MacStudio2 Git identity. The Stage A Codex CLI implementation integrated those proofs and produced the Reg bindings. The repair Codex CLI implementation applied Mathlib's disjoint-sum connectivity theorem at the three joins. [Experiment commit](https://github.com/the-omega-institute/trureturing-experiments/commit/6ef92106b2636a4c2e3a926bb6ce384abb1fdf8a) · [Push activity](https://github.com/the-omega-institute/trureturing-experiments/activity?ref=refs%2Fheads%2Fexp%2Fop-07b67e50-batch1) · [Original counting argument](https://github.com/the-omega-institute/trureturing/issues/31895) · [Prospective checkpoint](https://github.com/the-omega-institute/trureturing/issues/31895#issuecomment-7076815321)

Kramer’s Lemma 2.1 supplies related marked-cycle counts in his work on pendant-edge contraction. His two-path construction credits Proposition 5.1 of Cambie, Jooken and Wagner. [Kramer](https://hexagonmath.org/2611.00151v2)

## Triage

### What the settlement shows

- **Proved in Lean.** On the fixed connected host, `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv` and `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv` classify the actual objects. The corresponding `supportEquiv_order` and `treeFiberEquiv_order` laws give their pointwise orders. `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.induced_exact_moments` and `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.tree_exact_moments` give the four integers above. The same module's `exactGap` proves the exact positive difference and `result` refutes the universal comparison in Question 1.9.
- **Proved by arithmetic from the four exact moments.** Every support contributes one baseline tree. The additional tree copies have mean order $(61323620645707018-43855001336852520)/(14578492765509-10425438990512)$, strictly below the support mean. Reweighting by the number of trees therefore lowers the mean on this graph. When the core is proper or absent, selecting the full triangle triples a support’s weight. There are $501^2$ supports containing both full cycles, with mean order $5503$ from the two independent prefix lengths. Among supports with the full core there are $5\cdot501^2$ supports in all, so the full-core counts and orders follow by summing the five rooted triangle choices. Subtracting the extra copies of these full-core supports from the total extra count and order leaves $2\cdot 2072134997501$ copies of total order $2\cdot 8710145475410003$ carrying the full triangle and no full core. Their mean is about 3.0733 below the support mean. Their downward contribution exceeds the upward contributions of the two full-core classes.
- **Proved in the paper.** For trees, $\mu(T)=\operatorname{av}(T)$ because a connected vertex support has exactly one spanning tree. Theorem 1.2 independently proves the path minimum for $\mu$ at each fixed order, with equality only for the path. The counterexample rules out the proposed alternative derivation through Question 1.9. [Introduction and Theorem 1.2](https://arxiv.org/pdf/2508.20593v2#page=3)
- **Computed.** Running `python3 check.py` exited 0 with script SHA-256 `1320527deb25722d7a27f9a2a6cc246c5aa09ada11f9dbb27dfb85d807bbe9db`. It checked the path equalities for orders 1 through 8, enumerated actual vertex and edge subsets at $t=1$, compared direct intervals with marked-gap counts for $t=1,2,3,4$, and checked the moment polynomials against the marked-gap formulas at $t=1$ through $6$. It also checked the polynomial cross-product coefficientwise, the positivity of the shifted coefficients, the leading-coefficient ratio $79/28884$, and the exact gap at $t=500$. [Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/6ef92106b2636a4c2e3a926bb6ce384abb1fdf8a/docs/reports/cambie2508q19)
- **Open in this Lean development.** The uniform graph-to-moment classification for the proposed family $G_t$, the resulting gap for every $t\ge 500$ and its proposed asymptotic growth remain outside the compiled fixed-graph result. The unicyclic comparison and the smallest counterexample also remain unresolved here. [Parameterized argument and its scope](https://github.com/the-omega-institute/trureturing/issues/31895)

## ASSUMED-UNVERIFIED

The literature screen on #31895 located no independent answer in the sources it could inspect, including the arXiv versions, the available forward citations and the checked Lean settlement indexes. Some searches were rate-limited or inaccessible. Global priority, earlier private proofs and the precise execution time of the original experiment remain unverified. [Literature and experiment record](https://github.com/the-omega-institute/trureturing/issues/31895)
