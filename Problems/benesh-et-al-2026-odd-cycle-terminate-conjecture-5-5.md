---
slug: benesh-et-al-2026-odd-cycle-terminate-conjecture-5-5
bibkey: beneshernstmeyersalmonsieben2026geodeticremoving
doi: 10.48550/arXiv.2606.05483
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/OddCycleTER.conjecture_5_5
url: https://arxiv.org/abs/2606.05483v1
---

## Problem

Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon and Nándor
Sieben, *Impartial geodetic removing games on graphs*, arXiv:2606.05483v1,
§5.1, Conjecture 5.5, printed page 7.

> For cycle graphs with odd $n$, $\operatorname{nim}(\operatorname{TER}(C_n))=0$.

Section 5.1 defines $C_n$ for $n\ge4$. The assertion quantifies over every
natural $m\ge2$ and asks for the initial Grundy value on the fixed
undirected cycle $C_{2m+1}$. [Pinned paper](https://arxiv.org/pdf/2606.05483v1#page=7)

## Motivation

The block characterization and cyclic-rank response give a uniform
strategy in the original game. The response depends on the current
survivor order. The earlier fixed matching strategy has a counterexample.
[Fixed matching counterexample](https://github.com/the-omega-institute/trureturing/issues/31528#issuecomment-6985435536)

## Gap

The paper reports verification through $n=21$ and asks for a settlement
for the whole family in §6(1). The finite study at #31523 was scoped to
$C_{23}$ with $C_{21}$ calibration. The symbolic target at #31530
requires the original shortest-path hull and every legal move for all
$m\ge2$. The paper's Proposition 5.3 treats the avoidance game DNT,
whose rule excludes terminating moves. Proposition 5.4 treats even
cycles in TER. The cited hypergraph result requires pairwise disjoint
maximal stable sets, a hypothesis that fails for the screened odd cycles.
[Source and bounded literature screen](https://github.com/the-omega-institute/trureturing/issues/31523)
[Symbolic successor](https://github.com/the-omega-institute/trureturing/issues/31530)

## Route

A position is live exactly when each block of $m$ consecutive vertices
meets the survivor set. A vacant block puts all survivors in a
geodetically convex complementary arc of $m$ edges. Conversely, each
nonsurvivor is bracketed by survivors at cyclic distance at most $m$
along its containing gap. The hull contains the shortest path between
them.

Maintain $2k+1$ survivors with at least $k$ in each $m$-vertex block.
The first move leaves each block occupied. For $k>2$, choose the
$k$th survivor clockwise after the first deleted vertex, using the
pre-move order. Between the deleted vertices the two directed strict
arcs have $k-1$ and $k$ survivors. A block containing both endpoints
contains one of these arcs, so it loses two survivors only if it
started with more than $k$. The reply leaves $2(k-1)+1$ survivors
and at least $k-1$ in each block.

At $k=2$ the first move leaves four survivors. The complement of any
one survivor splits into two disjoint $m$-vertex blocks. Each meets
the other three survivors, so one contains exactly one. Deleting that
survivor is legal and leaves a proper hull. Strong induction gives
a zero-valued legal reply to each first move, and mex gives value zero
at every invariant position. Initially $k=m$.
[Symbolic proof](https://github.com/the-omega-institute/trureturing/issues/31530#issuecomment-6986118487)

## Falsifier

An $m\ge2$ with nonzero initial Grundy value in the original game
would refute Conjecture 5.5. For the proof route, a failure of the
full-hull equivalence, an invariant position with a first deletion
that ends play, or a first deletion with no reply satisfying the
applicable base or induction condition would invalidate the
corresponding step.

## Evidence

The theorem is `OddCycleTER.conjecture_5_5`. Its source
correspondence is as follows.

| Source clause | Lean counterpart |
| --- | --- |
| Fixed undirected $C_{2m+1}$ for every $m\ge2$ | Mathlib's `SimpleGraph.cycleGraph (2 * m + 1)` on `OddCycleTER.Vertex m`, with $m$ and $2\le m$ quantified by the theorem |
| Geodetic hull of the unselected vertices | `geoHull` on the survivor set, using all shortest paths in the original graph |
| Any unselected vertex may be selected at a live position | `moves` permits every single erasure when the origin has full hull |
| A move to proper hull wins and ends play | The erasure is legal from its full-hull origin. A proper-hull destination has no options |
| Initial value by minimum exclusion of option values | `grundy` recurses on survivor cardinality. `terNim` complements the selected set. The theorem starts at the empty selected set |

## Triage

- **Proved.** The uniform symbolic result gives zero initial
  Grundy value for every odd cycle in the source family. The induction also
  gives zero at each position satisfying the block invariant. It answers
  the odd-cycle question in §6(1). The other graph families asked about
  there are outside its scope.
- **Tier 2 (historical finite study).** Issue #31523 classified its finite
  $C_{23}$ study as computational frontier. Its computational result
  gives initial Grundy value zero on $C_{23}$.
  [Finite result](https://github.com/the-omega-institute/trureturing/issues/31523#issuecomment-6985091688)

## ASSUMED-UNVERIFIED

The bounded screen found no prior settlement in the material inspected.
A citing item indexed against the same-title SSRN record remains uninspected.
The OpenAlex citing-items query was rate limited. Literature priority remains unresolved. [Search scope](https://github.com/the-omega-institute/trureturing/issues/31523)
