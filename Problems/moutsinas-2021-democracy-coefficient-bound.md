---
slug: moutsinas-2021-democracy-coefficient-bound
bibkey: moutsinas2021hierarchy
doi: 10.1038/s41598-021-93161-4
url: https://arxiv.org/abs/1908.04358v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.result
---

# A directed graph with democracy coefficient above one

## Problem

G. Moutsinas, C. Shuaib, W. Guo and S. Jarvis (arXiv:1908.04358,
physics.soc-ph; Sci. Rep. 11, 13943 (2021)) define hierarchical levels of the
vertices of a weighted simple directed graph. With in-degrees
`d_j = Σ_i a_ij` and `M = (diag(d) − A)ᵀ`, the forward levels `g` are the
minimum-norm minimizer of `‖M x − d‖₂`, and the forward democracy coefficient
is `η_f = 1 − Mean(g_j − g_i)`, the mean over the arcs `i → j` weighted by
`a_ij`; the backward coefficient `η_b` uses out-degrees. The paper proves
`η_f, η_b ≥ 0` for weakly connected graphs and `η_f = η_b = 1` for balanced
graphs, and states:

> Let $G$ be a weakly connected directed graph. Then the following are true:
> $\eta_f(G) \le 1$ and $\eta_b(G) \le 1$; $\eta_f(G)=\eta_b(G)=1$ if and only
> if the graph is balanced.

Issue #11800 fixes the reading: weighted simple directed graphs with
antiparallel arcs allowed, weak connectivity of the underlying graph, the
levels as in the paper's Definition 3.1 without assuming uniqueness, and the
first bullet's forward inequality as the target. The result refutes it.

## Motivation

The democracy coefficient measures how much the vertices that drive a network
are themselves influenced, and the conjectured bound `η ≤ 1` would make `1`
the value of perfectly democratic, balanced networks; the paper derives from
it the bound `η(G) ≤ 1 − m/n` relating the coefficient to its influenced
subgraph. The frozen declaration
`D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.result` shows a
weakly connected unweighted graph on six vertices with `η_f = 901/898`.

## Gap

Issue #11800 preregisters the reading, the counterexample and the literature
check. The conjecture is in the latest arXiv version and in the journal
version. Semantic Scholar lists 26 citing records; the four with arXiv
identifiers were searched, and only one uses the democracy coefficient, as an
applied measure, without discussing the conjecture. Web searches for the
democracy coefficient together with conjecture or counterexample return only
the paper, its PMC copy and the authors' code.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Take the unweighted arcs `1→4, 1→5, 2→6, 3→6, 4→5, 4→6, 5→1, 5→2, 5→3,
   5→4, 6→1, 6→5`, weakly connected through `1–4, 1–5, 5–2, 5–3, 5–6`, with
   `d = (2, 1, 1, 2, 3, 3)`.
2. `g = (227, −991, −991, 329, 767, 659)/2694` satisfies `Mᵀ(M g − d) = 0`,
   so `‖M x − d‖² = ‖M g − d‖² + ‖M (x − g)‖²` for every `x`.
3. A minimizer `x` has `M (x − g) = 0`, whose solutions are `x = g + c𝟙`;
   since `Σ g_i = 0`, `‖x‖² = ‖g‖² + 6c²`, so `g` is the minimum-norm
   minimizer.
4. `Σ_{arcs}(g_j − g_i) = −18/449` with total weight `12`, so
   `η_f = 1 + 3/898 = 901/898`.

## Falsifier

The answer would change if the graphs were required to have no pair of
antiparallel arcs: every counterexample found has one (see Triage). The paper
allows such pairs, turning an undirected edge into two opposite arcs and
stating that undirected graphs have democracy coefficient `1`. It would also
change if the mean were taken over the set of distinct differences rather
than weighted by the arcs; the paper weights it by the arcs, and the graph
`G₆′` of the Triage exceeds `1` under both readings.

## Evidence

Exact SymPy arithmetic (issue #11800) gives `g = M⁺d` as above,
`η_f = 901/898` and `η_b = 343/354`. As controls, the same code reproduces the
paper's printed values: `(0, 0)` for the directed 3-chain, `(4/5, 4/5)` for
the 3-cycle with one arc of weight `1/2`, and `(1, 1)` for the balanced
3-cycle. The authors' released code returns `1.003340757238` on the graph
(scout reading).

The canonical source is
`D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.lean`. Its public
declarations are `indeg`, `lapT`, `residual`, `IsForwardLevels`,
`forwardDemocracy`, `WeaklyConnected`, `claim` and `result`. The frozen module
state has statement identity
`sha256:f0dfd18e704c2ba10a0e888b1dc04f0579389f98a2de26f8f63b891a956724b8`.
The result declaration has statement identity
`sha256:8d5e2a65d9febea4853d483e6cb4a35ec11730128f013b174d4d20cd9c8d7821`.
The Freeze event is
`sha256:84ff169d89d87dcf940fbde5a069b7a791df552658fafd8b790dc8738cb57e98`.
It has no project-level frozen prerequisites (pinned Mathlib only). The proof
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`;
no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2019 physics.soc-ph paper, preregistered in issue
#11800 before any Lean. `theorem`; resolution `refuted`. The public theorem
has `proof_shape: bind-only`: it evaluates the definitions at the explicit
graph and level vector. Its admission basis is `open-problem-resolution`.
Utility `kind=certified-instance; basis=refutes` with typed `claim` and
`result`.

### What the settlement shows

**Proved (Lean):** a weakly connected unweighted graph on six vertices has
forward democracy coefficient `901/898 > 1`, so the forward half of the first
bullet of Conjecture 3.6 fails.

**Mechanism (argument, not formalized):** with out-degrees `δ_i = Σ_j a_ij`
and total weight `W`, `Σ_{i,j} a_ij (g_j − g_i) = (d − δ)·g`, so
`η_f = 1 − (d − δ)·g / W` and `η_f ≤ 1` is the inequality `(d − δ)·g ≥ 0`.
For a balanced graph `d = δ` and `η_f = 1`. When `M x = d` is solvable, summing
its coordinates gives `(d − δ)·g = W` and `η_f = 0`. In the counterexample the
system is inconsistent (the least-squares residual is
`−(2/449)(530, 371, 371, 477, 583, 371)`), `d − δ = (0, 0, 0, 0, −1, 1)`, and
the levels place vertex 5, which has one surplus out-arc, above vertex 6,
which has one surplus in-arc: `(d − δ)·g = g_6 − g_5 = −18/449 < 0`.

**Computed (NumPy, not formalized):** over all weakly connected labelled
directed graphs on at most four vertices, both coefficients are at most `1`,
and `η_f = 0` whenever `M x = d` is solvable. The transpose of the
counterexample has `η_b = 901/898`, so the backward inequality fails as well.

**Computed (scout readings, not recomputed here):** no counterexample exists
on five or fewer vertices; on six vertices there are 54 among the 1,530,843
isomorphism classes of weakly connected unweighted directed graphs (generated
with nauty `geng -c | directg`), all strongly connected and all with an
antiparallel pair, the largest coefficient being `103/102`. The graph `G₆′`
with arcs `1→3, 1→4, 1→6, 2→5, 3→4, 3→5, 3→6, 4→1, 4→3, 4→6, 5→1, 5→6, 6→1,
6→2, 6→3, 6→4, 6→5` has all arc differences distinct and `η_f = 103/102`. For
oriented graphs (no antiparallel pair) no counterexample exists on seven or
fewer vertices.

**Source consequences (argument, not formalized):** the paper's derived bound
`η(G) ≤ 1 − m/n`, stated "if the above upper bounds are correct", fails for
the counterexample, since `1 − m/n ≤ 1 < 901/898`. Its theorems
`η_f, η_b ≥ 0` and `η = 1` for balanced graphs do not depend on the
conjecture and stand.

**Open:** the bound `η ≤ 1` for oriented graphs; the second bullet of
Conjecture 3.6, that `η_f = η_b = 1` only for balanced graphs; and the
supremum of `η_f` over weakly connected graphs.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
