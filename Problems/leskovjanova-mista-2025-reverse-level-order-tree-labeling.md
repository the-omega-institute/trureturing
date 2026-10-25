---
slug: leskovjanova-mista-2025-reverse-level-order-tree-labeling
bibkey: leskovjanovamista2025gaussiangme
doi: 10.22331/q-2025-08-27-1837
url: https://arxiv.org/abs/2401.04376v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.result
---

# Reverse level order labeling gives one nonzero entry in every nonfinal column tail

## Problem

O. Leskovjanová and L. Mišta Jr., *Minimal criteria for continuous-variable genuine multipartite entanglement*, arXiv:2401.04376v3; Quantum 9, 1837 (2025), Section 4.1.3, “Generic tree”, state the conjecture in `Quantum-accepted.tex`, lines 837–839:

> We checked by a direct calculation that for all configurations of up to $N=10$ the established reverse level order labeling leads to an adjacency matrix, where each vector $A_{i+1:N,i}$ contains only
> one non-zero component and therefore the respective quadrature combinations (\ref{uxpi}) contain at most two non-zero terms. This leads us to a conjecture
> that this statement holds generally for an arbitrary $N$-vertex tree.

The source construction, lines 828–835, roots the tree at its center vertex or at an endpoint of its central edge, assigns label $N$ to the root, and assigns decreasing labels level by level, from left to right within each level. The paper assumes $N\ge3$ for its entanglement application (lines 429–431). The source quotations and bibliographic entry are also in [the literature note](../Library/GraphInvariants/leskovjanovamista2025gaussiangme.md). The checked TeX member has MD5 `b1e8a86c3fefec6858c4ac36ca46f9fd`.

Issue [#21778](https://github.com/the-omega-institute/trureturing/issues/21778) fixes the graph statement with an arbitrary root and arbitrary order within each level. In the module, for every $n\in\mathbb N$, every simple graph $g$ on $\operatorname{Fin} n$ with decidable adjacency and $g.\mathrm{IsTree}$, every root $r\in\operatorname{Fin} n$, and every bijection $\ell:\operatorname{Fin} n\simeq\operatorname{Fin} n$ satisfying

$$
\operatorname{dist}_g(r,u)<\operatorname{dist}_g(r,v)
\ \Longrightarrow\ \ell(v)<\ell(u),
$$

define $A^\ell_{ji}$ to be the natural-valued adjacency entry of $g$ at $\ell^{-1}(j),\ell^{-1}(i)$: it is $1$ for adjacent vertices and $0$ otherwise. Then `claim` states

$$
\forall i\in\operatorname{Fin} n,\quad
i.\mathrm{val}+1<n\ \Longrightarrow
\exists! j\in\operatorname{Fin} n,\quad i<j\ \land\ A^\ell_{ji}\ne0.
$$

The domain preorder in `StrictAnti` is lifted along $\operatorname{dist}_g(r,\cdot)$; its codomain has the usual label order. Thus equal levels impose no label comparison. Lean's labels $0,\ldots,n-1$ correspond to the source's $1,\ldots,N$. The graph statement is proved by `result : claim`; the Cholesky and quadrature implications are outside that declaration.

## Motivation

Leskovjanová and Mišta Jr. (2025, arXiv:2401.04376v3), Section 4.1, represent a minimal set of two-mode marginal covariance matrices by a tree. They use its adjacency matrix to prescribe the off-diagonal support of positive-definite witness matrices. Their Appendix B transfers at most one nonzero entry in each strict lower column tail to the Cholesky factors, giving quadrature combinations involving at most two modes. A graph statement valid for every tree size supplies the combinatorial input to this generic-tree construction beyond the finite enumeration reported by the authors. It does not itself establish entanglement detection for a particular state.

## Gap

The bounded literature check before any Lean is recorded in #21778:

- The orchestrator reports that arXiv v3 retains the conjecture, that Crossref identifies the Quantum publication, that a web search for “reverse level order” with the authors' names returned the source and unrelated GME papers, and that Zenodo returned zero records for that phrase.
- The issue attributes to its search contributor checks of citing works arXiv:2412.09757, arXiv:2510.26762 and arXiv:2510.26761, and the later Leskovjanová paper arXiv:2605.28404, with no discussion of tree orderings; it also reports no match in MathDB or `google-deepmind/formal-conjectures`.
- The preregistration reports no existing repository issue, module, Library note or dossier addressing the question.

`not-found-in-searched-scope`. The v3 conjecture is verified against the source text; the other search readings remain attributed to #21778.

## Route

Fix $n\in\mathbb N$, a simple graph $g$ on $\operatorname{Fin} n$ with decidable adjacency, a proof $h_T:g.\mathrm{IsTree}$, a root $r$, and a bijection $\ell$ strictly antitone for the distance-lifted domain preorder and the usual label order.

1. **Unique parent.** For a vertex $v\ne r$, `unique_parent h_T r v` establishes exactly one neighbor $w$ with $\operatorname{dist}_g(r,w)+1=\operatorname{dist}_g(r,v)$. It obtains a first edge of a shortest walk from $v$ to $r$. Under the tree hypothesis, `SimpleGraph.IsTree.dist_eq_dist_add_one_of_adj` says that the distances of adjacent vertices from $r$ differ by one; uniqueness of the path from $v$ to $r$ identifies any two candidate first neighbors.
2. **Larger labels.** For adjacent vertices $v,w$, `larger_label_iff_parent`, under the same tree and strict-antitonicity hypotheses, establishes $\ell(v)<\ell(w)$ if and only if $\operatorname{dist}_g(r,w)+1=\operatorname{dist}_g(r,v)$. The adjacency hypothesis is essential to this equivalence.
3. **The column vertex.** For $i\in\operatorname{Fin} n$ with $i.\mathrm{val}+1<n$, `column_vertex_ne_root`, under the same tree, root, bijection and strict-antitonicity hypotheses, establishes $\ell^{-1}(i)\ne r$. If it were the root, the vertex with label $i.\mathrm{val}+1$ would have positive distance from it; strict antitonicity would force that larger label below $i$.
4. **The tail.** For any $i\in\operatorname{Fin} n$ whose vertex satisfies $\ell^{-1}(i)\ne r$, `column_tail_unique`, under the same tree, decidable-adjacency, root, bijection and strict-antitonicity hypotheses, takes its unique parent $w$. The row $j=\ell(w)$ is larger than $i$ and its natural-valued adjacency entry is $1$. Conversely, a nonzero entry at a row $j>i$ gives an adjacent vertex; `larger_label_iff_parent` makes it a parent, and `unique_parent` identifies it with $w$. Applying the bijection gives uniqueness of $j$.

`result` applies the fourth step using the nonroot condition supplied by the third.

## Falsifier

A counterexample to `claim` would require a finite simple tree, a root, a bijection satisfying the stated strict level decrease, and a label $i$ with $i.\mathrm{val}+1<n$, whose strict lower column tail has either zero nonzero entries or more than one. The matrix is the ordinary zero-one adjacency matrix with both indices transported by $\ell^{-1}$; the distance order is measured from the chosen root.

The last column is excluded, since it has no row with a larger label. For $n=1$ there is no eligible column; for $n=0$ there is no root in $\operatorname{Fin} n$. Neither case asserts the existence of a parent for an isolated vertex. The statement concerns adjacency support, with no assertion about the values of witness-matrix coefficients or about quantum states.

## Evidence

The canonical source is `D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.lean` (117 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling.lean.json`, statement `sha256:09fe786fbc123dc1774bdedef1ff68b3904c8535968e10bd4b401530303801d3`.

Declaration statements:

- `result`: `sha256:665dd8bbd071f27290a40f58a8285a97c66087fb2bb9390d3125a125a3aa5e6b`;
- `claim`: `sha256:e8206703551074a5cb74b9611c24ae10b8689645431d3d015439315e5152e356`.

## Triage

Tier 1 conjecture of a 2024 preprint kept in the 2025 journal version, preregistered in issue #21778 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\in\mathbb N$, every simple graph $g$ on $\operatorname{Fin} n$ with decidable adjacency that is a tree, every root $r$, and every bijection $\ell$ strictly decreasing with distance from $r$, each label $i$ with $i.\mathrm{val}+1<n$ has exactly one larger row label $j$ with a nonzero natural-valued adjacency entry at $\ell^{-1}(j),\ell^{-1}(i)$. No central-root or within-level ordering condition is imposed.

**Computed, not formalized** (exact integer adjacency counts, in the source's one-based labels):

- The one-vertex graph has tail-count list $(0)$, including its final column; there is no nonfinal column to test.
- The triangle on labels $1,2,3$, rooted at $3$, has levels $(1,1,0)$ and a strictly level-decreasing labeling, but tail counts $(2,1,0)$. This is an explicit example outside the tree hypothesis.
- The four-vertex star with center labeled $1$ and leaves labeled $2,3,4$, rooted at its center, has tail counts $(3,0,0,0)$. Its labeling does not decrease with level.
- The seven-vertex tree with edges $\{7,6\},\{7,2\},\{7,1\},\{6,5\},\{6,4\},\{6,3\}$, rooted at $7$, has levels $(1,1,2,2,2,1,0)$ and tail counts $(1,1,1,1,1,1,0)$. Its labeling does not decrease with level: for example, label $1$ lies nearer the root than label $3$. These counts concern only the specified examples.

**Argued, not formalized.**

- *A wider sufficient order.* For a finite nonempty rooted tree, it suffices that a bijective labeling place each nonroot vertex's parent above that vertex. To see why, deleting any tree edge separates its endpoints. The unique path from the root to the endpoint in the other component crosses that edge, so every edge joins a parent to a child. A nonroot vertex therefore has its parent as its only higher-labeled neighbor; all its children have smaller labels. Labels strictly increase along the root path, so the root is largest. This gives the same column-tail property for this weaker ordering requirement by an argument not formalized here. The module's `claim` retains the stronger level-decreasing condition.
- *A neighbouring converse.* In a finite nonempty simple graph with distinct labels, suppose every vertex except the largest-labeled one has exactly one higher-labeled neighbor. Orient each edge toward its larger endpoint. Following outgoing edges strictly increases the label and must end at the largest vertex, since every other vertex has an outgoing edge. Thus the graph is connected. A cycle would have a smallest-labeled vertex with two higher-labeled neighbors on that cycle, a contradiction. Hence the graph is a tree, and the orientation points toward the largest vertex as root. Together with the preceding argument, this characterizes the one-higher-neighbor orderings without requiring a global comparison between different branches' levels.
- *Boundary of the count.* The final tail is empty by its index range, so it cannot be included in an exactly-one assertion. A one-vertex tree has no nonroot vertex and no nonfinal column. The triangle and star calculations distinguish two ways to leave the proved hypotheses; they do not classify all such departures.
- *Effect on the paper.* For the source's simple trees on $N\ge3$ vertices with decidable adjacency, any root and a bijective labeling strictly decreasing with distance from that root, `result` supplies the graph support condition. For real symmetric positive-definite matrices $Z_A^\alpha$, $\alpha\in\{x,p\}$, whose off-diagonal support is contained in that labeled adjacency support, each strict lower column tail therefore has at most one nonzero entry. The argument of Leskovjanová and Mišta Jr. (2025, arXiv:2401.04376v3), Appendix B, lines 2091–2125, can be read directly from the Cholesky recurrence: inductively, each earlier column of $L^\alpha$ has at most one nonzero entry below its diagonal, so for $j<i<k$ the product $L^\alpha_{ij}L^\alpha_{kj}$ vanishes. The correction sum is zero and $L^\alpha_{ki}=(Z_A^\alpha)_{ki}/L^\alpha_{ii}$; positive definiteness gives $L^\alpha_{ii}>0$. Thus each Cholesky tail has at most one nonzero entry, and each source quadrature combination has its diagonal term and at most one further term. The last combination has only its diagonal term. This supplies the previously conjectural graph input for arbitrary tree size in that construction. The Cholesky transfer, the sum and product GME inequalities, and detection of particular states are not conclusions of `result`; their other analytic and physical assumptions remain necessary.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. Apart from the v3 source quotation, the arXiv-version listing, Crossref reading, web and Zenodo searches, checks of the four other papers identified in #21778, MathDB and `google-deepmind/formal-conjectures` searches, and the preregistration's repository-wide absence reading were not independently reproduced. They remain reports attributed to #21778.

The authors' reported enumeration through $N=10$ was not reproduced. The four explicit adjacency calculations above are finite computations, not Lean proofs or an enumeration of other tree sizes. The wider parent-order condition, its converse characterization, and the Cholesky/quadrature transfer are arguments given above but are not formalized by this module. No conclusion about singular positive-semidefinite witness matrices or the detectability of a specified quantum state is supplied by `result`.
