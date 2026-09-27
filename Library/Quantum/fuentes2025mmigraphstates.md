---
bibkey: fuentes2025mmigraphstates
authors: Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack
year: 2025
title: "Monogamy of Mutual Information in Graph States"
doi: 10.48550/arXiv.2511.19585
url: https://arxiv.org/abs/2511.19585v1
claim: "The paper reads MMI violation in graph states as a forbidden-subgraph phenomenon and conjectures (Conjecture 1, Forbidden-Subgraph) that any graph state that violates MMI has a graph representation that is LC-equivalent to a graph H containing a K_4 subgraph, the four-vertex star, with H a generalized star graph with respect to some partition; it verifies the conjecture exhaustively up to 8 qubits."
strata_touched:
  - D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph
license: citation-only
triage: anchor
---

# Monogamy of Mutual Information in Graph States

The paper computes the entanglement entropy of a graph state from the
adjacency matrix of its graph (eq. `EEadj`):

> For a graph $G$ with vertex set $V = \{n\}$ and adjacency matrix
> $\Gamma_G$, let $\{A, \overline{A}\}$ be any bipartition of $V$. The
> entanglement entropy of $A$, in $\ket{G}$, is calculated from $\Gamma_G$ as
> $S_A(\ket{G}) = \text{rank}_{\mathbb{Z}_2}(\Gamma_{G}^{A \, \overline{A}})$.

and states MMI (eq. `MMI`) as

> For an $n$-party system with pairwise-disjoint subsystems $I,\ J,$ and $K$,
> MMI requires $S_{IJ} + S_{IK} + S_{JK} \geq S_I + S_J + S_K + S_{IJK}$.

Local Clifford operations act on graph states as local complementations:
"we use $LC$ to refer interchangeably to local Clifford equivalence and local
complementation equivalence in graph states". The symbol $K_4$ denotes the
four-vertex star: "the graph state $\ket{K_4}$, representable by the
$4$-vertex star graph $K_4$".

A generalized star graph $\mathcal{G}$ has a central subgraph $C$ connected to
$k$ non-empty subgraphs $\mathcal{G}^1, \dots, \mathcal{G}^k$ that are
vertex-disjoint and mutually disconnected, with $\{C, V^1, \dots, V^k\}$ a
partition of $V$. After eq. `K4Inclusion` the paper notes: "the existence of
a $K_4$ subgraph guarantees that there exists a partition under which the
graph is (nontrivially) of type $\mathcal{G}$, since we can place the central
vertex of $K_4$ in $C$, place each leaf of $K_4$ in $I,\ J,$ and $K$,
respectively, and place all remaining vertices of the graph in $C$."

The conjecture reads

> **Conjecture 1 (Forbidden-Subgraph).** Any graph state that violates MMI has
> a graph representation that is $LC$-equivalent to a graph $H$ containing a
> $K_4$ subgraph. $H$ is $\mathcal{G}$ with respect to *some* partition.

and the discussion describes it as positing "the necessity of an induced
four-star in the LC orbit of any graph whose associated graph state violates
MMI". The paper reports "We exhaustively verify this conjecture up through
$n=8$ qubits".

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2511.19585
- URL: https://arxiv.org/abs/2511.19585v1
- Version and location: arXiv:2511.19585v1 (2025-11-24), the only version
  listed by the arXiv API on 2026-09-27; source file `paper.tex`, eq. `MMI`
  (line 405), the LC paragraph (line 546), eq. `EEadj` (lines 590–600), the
  generalized star definition (lines 1452–1466), eq. `K4Inclusion` and the
  partition remark (lines 1974–1980), Conjecture 1 (lines 2400–2403) and the
  discussion (line 2435).
