---
slug: becker-cameron-hanely-ong-previte-conjecture-31
bibkey: becker2024minimalforts
doi: 10.48550/arXiv.2404.05963
url: https://arxiv.org/abs/2404.05963v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MinimalForts/EveryOrder.result
---

# Becker–Cameron–Hanely–Ong–Previte Conjecture 31

## Problem

Paul Becker, Thomas R. Cameron, Derek Hanely, Boon Ong and Joseph P. Previte,
*On the number of minimal forts of a graph*, arXiv:2404.05963v1, Section 6:

> There exists a family of graphs $G_n$ such that
> $3^{1/3}<\lim_{n\to\infty}|\mathcal F_{G_{n+1}}|/|\mathcal F_{G_n}|<2$,
> where $2$ is the asymptotic growth rate of Sperner's bound.

The source graphs are finite, simple, undirected, loopless and unweighted.
A fort is nonempty, and each vertex outside it has a number of neighbors in it different
from one. The family $\mathcal F_G$ contains **all** inclusion-minimal forts.
The conjecture sentence does not separately require $|V(G_n)|=n$.

## Motivation

`D5/S3/Combinatorics/MinimalForts/EveryOrder.result` supplies the stronger every-order
existence statement: for every positive $n$, the graph is connected, has exactly $n$ vertices,
and has positive full minimal-fort count $A_n$. It gives
$A_n/(3/2)^n\to1$ and the full successive ratio $A_{n+1}/A_n\to3/2$, with
$3^{1/3}<3/2<2$.

## Gap

Preregistration [#23336](https://github.com/the-omega-institute/trureturing/issues/23336)
fixes the complete source problem and every-order target. Nguyen Hoang Dat and Franklin H. J.
Kenter, arXiv:2605.07298v1, Section 5.2, Question 1, explicitly restate Conjecture 31 and report
unsuccessful attempts to exceed the cube-root-of-three growth rate. Later results on all forts,
trees and hypercubes address different statements. These are bounded standing observations,
not a worldwide absence or priority claim. The journal subscription body is unread.

## Route

1. Take disjoint blocks consisting of $x$ copies of $K_6$, $2y$ copies of $K_3$,
   $z$ octahedra $K_{2,2,2}$, and one $K_{r+2}$, and add a universal root.
   The actual order is $6(x+y+z)+r+3$ and the graph is connected.
2. Exhaustively characterize the two classes of minimal forts. Root-free counts add across
   components. Root-containing choices factor. The exact full count is
   $(r+2)6^x9^y12^z+15x+6y+11z+\binom{r+2}{2}$, including zero multiplicities.
3. Put $k=x+y+z$, $b=\log(2/3)$, $p=\log(4/3)$,
   $g=6\log(3/2)-\log9$ and $c_r=(r+3)\log(3/2)-\log(r+2)$.
   The ratio $b/p$ is irrational, and $0<g<p$ follows from $9<(3/2)^6<12$.
   Irrational rotation, a compact finite cover and finite-simplex minimization supply
   natural multiplicities at every $k$ with $xb+zp-kg-c_r\to0$ for each of the six residues.
4. For $n\ge3$, write $n-3=6k+r$, $0\le r<6$. The normalized exponential term is exactly
   the exponential of this error. The additive term is bounded by
   $15k+\binom{r+2}{2}$ and is negligible. Finiteness of the residue set combines the six
   tail estimates into the full limit. Complete graphs handle $n=1,2$.
   Positivity and normalization give the successive-ratio limit.

## Falsifier

The source correspondence would fail if the formal count selected only some minimal forts,
quotiented vertex subsets, used a different order, omitted positive orders, or assumed a graph
count in place of proving it. `minimalForts` filters every actual vertex subset using the reused
`IsFort` predicate and inclusion-minimality over all fort subsets. The graph count and order
are proved from the actual constructors. Both limits use the full natural filter at infinity.

## Evidence

`MixedBlocks.mixed_graph_count` proves the exact graph order, connectedness and full count
for arbitrary natural multiplicities and arbitrary natural $r$.
`BlockParameters.residue_sequences` supplies all six feasible sequences.
`CountAsymptotics.mixed_count_normalization` proves the actual count limit, and
`EveryOrder.result` combines every positive order, positivity, normalization, the full ratio
and the strict endpoint bounds. For every m at least two, `OctahedronBlock.equipartite_minimal_iff` and
`equipartite_rooted_iff` classify every actual subset of the complete equipartite graph
with m two-vertex parts. `equipartite_block` counts whole parts and transversals by
exhaustive bijections, giving m + 8*choose(m,3) and 4*choose(m,2). Its direct m=3
application supplies the six-vertex octahedral counts 11 and 12 in `mixed_graph_count`.

## Triage

The source is an externally stated existence conjecture. The formal result retains the whole
successive-ratio assertion and strengthens its graph-order and connectedness requirements.

### What the settlement shows

The proved existence assertion has limiting base $3/2$. It gives no extremal optimum and no
claim that every graph family has this growth rate. The source's explicit counts for its other
graph families are not changed.

## ASSUMED-UNVERIFIED

The literature scope is bounded to the accessible primary source, the stated open restatement,
and the source/title/fort-growth ownership searches. No claim is made about the unread journal
body or about all subsequent literature. Source-bound audit completion remains separately
tracked by [#23372](https://github.com/the-omega-institute/trureturing/issues/23372).
