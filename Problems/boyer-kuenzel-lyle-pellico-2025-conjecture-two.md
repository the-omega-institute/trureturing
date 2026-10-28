---
slug: boyer-kuenzel-lyle-pellico-2025-conjecture-two
bibkey: boyerkuenzellylepellico2025wellhued
doi: 10.48550/arXiv.2506.04993
url: https://arxiv.org/abs/2506.04993v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result
---

# Refuting the unrestricted well-hued graph characterization

## Problem

Geoffrey Boyer, Kirsti Kuenzel, Jeremy Lyle and Ryan Pellico,
*Well-hued graphs with first difference two*, arXiv:2506.04993v1,
Section 3, Conjecture 2, printed page 10, states:

> $G$ is a connected, well-hued graph with sequence
> $(\alpha(G), 2\alpha(G), 3\alpha(G), \dots, k\alpha(G))$
> and chromatic number $k$ if and only if it is a spanning subgraph of
> $K_{\alpha(G), \dots, \alpha(G)}$ such that for any $u \in V(G)$,
> the graph induced by $V(G) - N_G[u]$ is
> $\overline{K_{\alpha(G)}}$-free.

The quotation is from the version 1 TeX source, with display placement and
spacing normalized. Its arXiv page specifies CC BY-NC-SA 4.0. The overline
denotes an edgeless graph, so the forbidden induced set is independent.
There are `k` parts in the balanced multipartite host.

### Statement echo and clause correspondence

The sole target is the entire equivalence for every finite simple graph
`G` and every positive natural number `k`, with `alpha(G)` the independence
number. The surrounding section studies `alpha(G)=2`, but the paragraph
introducing Conjecture 2 explicitly generalizes the sequence to `alpha(G)`;
the next paragraph returns to the restricted case. The target is not the
restricted Theorem 4.

In the namespace
`D5.S3.Combinatorics.Graph.Products.BoyerKuenzelLylePellicoConjectureTwoRefutation`:

- `claim` quantifies `(V : Type) [Fintype V] [DecidableEq V]`,
  `(G : SimpleGraph V)` and `(k : Nat)`, with premise `0 < k`.
- `ProperColorable G j S` chooses a coloring `V -> Fin j` proper on the
  induced vertex set `S`. For positive `j`, every subset coloring extends
  outside `S`. Each test permits fresh recoloring.
- `MaximalColorable G j S` requires colorability and failure for every
  one-vertex extension. Heredity of induced colorability makes this
  equivalent to inclusion-maximality among all vertex supersets.
- `WellHued G` equates the orders of every pair of maximal induced
  `j`-colorable sets, for every `j >= 1`.
- `HasSequence G k` fixes that order to `j * G.indepNum` for
  `1 <= j <= k`. `HasChromaticNumber G k` provides a `k`-coloring and
  excludes every coloring with fewer than `k` colors.
- `LeftSide G k` is connectedness conjoined with these three properties.
- `BalancedMultipartiteSubgraph G k` gives `k` independent parts, each
  of size `G.indepNum`, pairwise disjoint and covering `V`; equivalently,
  `G` is a spanning subgraph of the required complete multipartite host.
- `AntiNeighborhoodFree G` excludes an independent `G.indepNum`-element
  set outside each closed neighborhood. `RightSide G k` conjoins it with
  the balanced-host condition.
- `claim` asserts `LeftSide G k <-> RightSide G k` under the above
  quantifiers; `result` has literal type `Not claim`.

## Motivation

The proposed characterization extends the paper's independence-number-two
result to arbitrary independence number. The three by three rook graph
meets the proposed right side with `k=3` but fails well-huedness. This
settles the printed unrestricted equivalence negatively while preserving
the distinction from the source's restricted results.

## Gap

The result supplies no corrected characterization, classification of all
counterexamples, or extension of Theorem 4. The rook-graph classification
and its non-well-hued structure are already due to Wayne Goddard, Kirsti
Kuenzel and Eileen Melville, *Well-hued graphs*, Discrete Applied
Mathematics 320 (2022), 370–380, DOI `10.1016/j.dam.2022.06.010`, Lemma 6
and Theorem 10. Only the connection refuting the named 2025 conjecture is
the resolution candidate; no new rook classification or priority is claimed.

## Route

`rookGraph` has vertex set `Fin 3 x Fin 3`. Distinct cells are adjacent
exactly when they share a row or a column. The private `rook_alpha` proves
independence number three using a diagonal witness, a finite upper-bound
certificate, and the pinned Mathlib independence-number API.

The private `rook_right` partitions the board by row plus column modulo
three. Its three independent triples are disjoint and cover the board.
For the antineighborhood condition, adjoining the center to a hypothetical
independent triple outside its closed neighborhood would exceed the
independence number.

The set `S={(0,0),(0,1),(1,0),(1,1),(2,2)}` induces a four-cycle plus an
isolated vertex. The set
`T={(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)}` induces a six-cycle. The proof
kernel-checks that both are maximal induced bipartite sets, allowing
arbitrary recoloring on every extension, and that their orders are five
and six. The reverse implication of `claim` would therefore force a false
equality. Every private helper is consumed by this single refutation.

## Falsifier

A proof of the entire printed equivalence would specialize at this graph
and `k=3`, implying `WellHued rookGraph`. Its maximal bipartite sets `S`
and `T` would then have equal orders. The compiled theorem `result`
proves the literal negation of that equivalence. The obstruction is a
failure of well-huedness, rather than an omitted connectedness clause.

## Evidence

- Primary source: https://arxiv.org/abs/2506.04993v1,
  Conjecture 2, printed page 10; DOI `10.48550/arXiv.2506.04993`.
- Known supplier:
  https://people.computing.clemson.edu/~goddard/papers/wellhued.pdf,
  Section 3.5, Lemma 6 and Theorem 10; DOI `10.1016/j.dam.2022.06.010`.
- Lean module:
  `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.lean`.
- Public settling theorem:
  `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result : Not claim`.
- The kernel report identifies the claim as a proposition and the result
  as its closed literal negation, with axiom closure contained in
  `Classical.choice`, `Quot.sound` and `propext`.
- The source definitions and their correspondence are stated above;
  the Blueprint gives the quantified equivalence and its negation.

## Triage

`theorem`, with outcome **refuted** for the whole Conjecture 2 in version 1.

### What the settlement shows

**Proved**, by
`D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result`:
the printed universal equivalence is false. Its proposed right side does
not suffice for well-huedness; maximal induced two-colorable sets may
have different orders. The finite certificates are consumed steps of
this theorem and are not additional resolved problems.

**Open here:** a corrected sufficient condition for the unrestricted
characterization, any classification of its counterexamples, and any
consequence for other conjectures. No new theorem about these questions
is asserted. The source's independence-number-two Theorem 4 is outside
the refuted assertion and is not contradicted by this example of
independence number three.

## ASSUMED-UNVERIFIED

The literature boundary is bounded to the primary version and its
context, the cited supplier, repository searches including private
definitions, pinned Mathlib graph sources, and accessible third-party
Lean searches. These searches found no exact whole-refutation theorem
to reuse. The third-party rook-graph definition and domination results
in `facebookresearch/atlas-lean` do not supply the required whole
refutation. No third-party proof was copied.

No exhaustive worldwide openness, errata coverage, priority or journal
novelty claim is established. The source attribution distinguishes the
known 2022 obstruction from the connection to the named 2025 statement.
The author PDF's availability is not treated as a code or text reuse
license; its contribution is summarized in original prose.
