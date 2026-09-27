---
slug: fuentes-2025-mmi-forbidden-subgraph
bibkey: fuentes2025mmigraphstates
doi: 10.48550/arXiv.2511.19585
url: https://arxiv.org/abs/2511.19585v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.result
---

# The forbidden-subgraph conjecture for MMI in graph states holds

## Problem

Fuentes, Keeler, Munizzi and Pollack (arXiv:2511.19585v1) conjecture:

> **Conjecture 1 (Forbidden-Subgraph).** Any graph state that violates MMI has
> a graph representation that is $LC$-equivalent to a graph $H$ containing a
> $K_4$ subgraph. $H$ is $\mathcal{G}$ with respect to *some* partition.

Issue #10534 fixes the readings from the paper: the entropy of a set of
qubits `A` is the rank over `Z_2` of the adjacency block with rows in `A` and
columns outside `A`; an MMI violation is a triple of pairwise disjoint sets
`I`, `J`, `K` with `S_IJ + S_IK + S_JK < S_I + S_J + S_K + S_IJK`; LC
equivalence is a finite sequence of local complementations; `K_4` is the
four-vertex star `K_{1,3}`, read as an induced subgraph, which is the stronger
reading; and a generalized star with centre `C` and parts `V^1, …, V^k` has
nonempty, pairwise disjoint parts that with `C` partition the vertices, no
edge between different parts, and an edge from every part to `C`.

## Motivation

The paper verifies the conjecture exhaustively up to eight qubits and leaves
larger graph states open.
`D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.result`
proves it for every number of qubits: every MMI-violating graph state reaches,
by local complementations, a graph with an induced four-star, which is a
generalized star for the partition that puts the three leaves in their own
parts and every other vertex in the centre.

## Gap

Issue #10534 preregisters the proof route and the literature check. arXiv
lists only version 1; the three citing papers reported by Semantic Scholar and
INSPIRE (arXiv:2608.17020, arXiv:2604.14271, arXiv:2510.15067) cite the paper
only in reference lists, and the authors' 2026 papers do not address the
conjecture. Kwon and Oum (Eur. J. Combin. 41 (2014) 100–127, arXiv:1306.3066,
Theorem 3.1(2)) prove that every connected graph with enough vertices has a
`K_n` vertex-minor, with an unspecified bound; `K_4` and the four-vertex star
are locally equivalent. The explicit bound of seven vertices and the list of
the connected graphs without a four-star vertex-minor used here are
`not-found-in-searched-scope`.

## Route

1. Local complementation at vertices of a vertex set commutes with
   restriction to that set, so an induced four-star, or a relabelling of a
   fixed graph, reached on part of the vertices lifts to the whole graph.
2. A connected graph has an ordering of its vertices in which every vertex
   after the first is adjacent to an earlier one. The graph on the first
   `m + 1` vertices is the graph on the first `m` with one new vertex adjacent
   to a nonempty set `T` of them, and local complementation at earlier
   vertices keeps `T` nonempty. For the representatives `K_1`, `K_2`, the path
   `P_3`, the path `P_4`, the 5-cycle `C_5` and the triangular prism, and every
   nonempty `T`, a listed sequence of at most three local complementations
   carries the extension to a graph with an induced four-star or to a
   relabelling of the next representative; every extension of the prism
   reaches an induced four-star. These 120 certificates are checked by
   evaluation. Hence a connected graph without a four-star vertex-minor has
   at most six vertices and is locally equivalent to a relabelled
   representative.
3. Local complementation at `v` changes the adjacency block of `A` by the
   row operation `1 + u e_vᵀ` (`u_v = 0`) when `v ∈ A`, an involution over
   `Z_2`, and by the corresponding column operation otherwise, so every
   entropy is unchanged; relabelling permutes rows and columns.
4. When a vertex set has no edge to its complement, the adjacency block of
   every `A` is block-diagonal after reordering, so the entropies add over the
   set and its complement.
5. The representatives satisfy MMI: for `K_1`, `K_2`, `P_3`, `C_5` and the
   prism the entropy of `A` is `min(|A|, n − |A|)`, by a checked parity
   criterion that makes the rows of `A` independent, and MMI then reduces to
   arithmetic; for `P_4` a violation needs four nonempty parts, hence single
   vertices, where the three pairs have entropies at least `2, 2, 1`.
6. If a graph state reached no induced four-star, every connected component
   would be locally equivalent to a relabelled representative (steps 1–2), so
   by steps 3–5 and induction on the number of vertices it would satisfy MMI.

## Falsifier

The proof would fail if a certificate did not check, if local
complementation changed some entropy, or if a representative violated MMI.

## Evidence

Exhaustive search with nauty `geng` over the connected graphs on `4` to `8`
vertices: the local-complementation orbits without an induced four-star are
the orbits of `P_4` (`n = 4`), `C_5` (`n = 5`) and the triangular prism
(`n = 6`), and there are none for `n = 7` (853 graphs) and `n = 8` (11117
graphs). No graph in these orbits violates MMI. The 5-cycle and the prism
give the absolutely maximally entangled states on five and six qubits.

The canonical source is
`D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lean`.
Its public declarations are `lc`, `lcSeq`, `IsClaw`, `entropy`,
`ViolatesMMI`, `IsGeneralizedStar`, `claim`, and `result`. The frozen module
state has statement identity
`sha256:81981077a3cd56f484109eb63008d9318f6a36c1c70e0df494f9f09515aef166`.
The result declaration has statement identity
`sha256:5685717741e6283d7382bd2db3f27e7d30d268b94ec809b0114eb4a1b0bdc566`.
The Freeze event is
`sha256:327c0570404b9ac857e7ddd982af73a180197bbbc816d647781967cc4de43657`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #10534 before the
probe. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the classification of step 2, the invariance of step
3 and the additivity of step 4 are new propositions on the live proof path.
Its admission basis is `open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The reading of the entropy, of LC equivalence and of the four-star follows
the paper; the bounded literature check does not establish exhaustive
worldwide novelty, priority, or the absence of an independent proof.
