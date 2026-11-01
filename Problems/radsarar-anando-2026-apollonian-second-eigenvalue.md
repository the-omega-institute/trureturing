---
slug: radsarar-anando-2026-apollonian-second-eigenvalue
bibkey: radsararanando2026apollonian
doi: null
url: https://mathoverflow.net/questions/516405
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed_degrees
  - D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_gram_offdiag
---

# Second adjacency eigenvalue of the inner-face Apollonian stages

## Problem

Rad Sarar Anando's MathOverflow question 516405, revision 1,
GUID `8C9D6CD5-E3A3-4B25-BDB6-FF5A9A3D3A2B`, asks whether the second largest
ordinary adjacency eigenvalue, counted with multiplicity, satisfies

$$\lim_{m\to\infty}\theta_2(G_m)/2^{m/2}=\sqrt2.$$

Here $G_0$ is plane $K_4$ with outer triangle $abc$ and centre $o$.
Every step inserts one vertex in each inner triangular face and joins it
exactly to the three corners; the outer triangle is never subdivided.
The [source note](../Library/GraphInvariants/radsararanando2026apollonian.md)
attributes the quotation and adapted exposition to the author under CC BY-SA 4.0.

## Motivation

The dominant old vertices have exponentially growing degree, while their
common late neighbours grow only linearly. A fixed old cutoff exposes this
separation through the Gram matrix of the old-to-late adjacency block.

## Gap

The graph-specific spectral limit remains to be linked to the finite
constructor and its degree, common-neighbour and orientation laws.
The full target quantifies along every natural stage, including odd stages;
a conditional estimate model or a finite computation does not settle it.
The forward preregistration is [issue #24989](https://github.com/the-omega-institute/trureturing/issues/24989).

## Route

Fix $k$ and partition stage $m>k$ into $H=V(G_k)$ and later vertices $L$.
The old-to-late block $B$ has Gram diagonal
$\deg_{G_m}(v)-\deg_{G_k}(v)$ and off-diagonal entries at most $2(m-k)$.
An inner vertex born at $j$ has degree $3\,2^{m-j}$; the centre has degree
$3\,2^m$ and each outer seed vertex has degree $2^{m+1}+1$.
Thus $2^{-m}BB^\top$ converges on fixed $H$ to a diagonal matrix whose second
largest entry is $2$.

Edges induced on $L$ orient from newer to older endpoints, with outdegree
at most $3$ and indegree at most $3\,2^{m-k-1}$. The directed-edge
Cauchy--Schwarz bound makes the normalized remainder at most
$3\sqrt2\,2^{-k/2}$ asymptotically. Ordered eigenvalue perturbation,
positive Gram/dilation spectrum with multiplicities, and then $k\to\infty$
give the accepted ordinary proof. This route does not assume its graph bounds.

## Falsifier

Changing the outer-face convention, inserting one random face at a time,
using weighted or normalized adjacency, replacing the ordered second
eigenvalue by the spectral radius, or proving only a finite-stage or
subsequence statement changes the question. The posted numerical values
and preliminary bounds are not assumptions.

## Evidence

The finite source construction and its graph laws belong to
[InnerFaceStages](../D5/S3/Combinatorics/Apollonian/InnerFaceStages.lean), with
their [canonical exposition](../Blueprint/D5/S3/Combinatorics/Apollonian/InnerFaceStages.md).
These combinatorial statements alone do not establish the spectral limit.
No frozen graph-specific spectral resolution is asserted here.

## Triage

The remaining spectral interfaces are the remainder operator-norm estimate
from the actual orientation, ordered positive-spectrum transport for the
unequal adjacency block with zero padding and multiplicity, the fixed-cutoff
Gram limit, and the all-natural-stage limit composition. Existing generic
perturbation, Gram multiplicity and scaling declarations are suppliers for
those interfaces, rather than a certificate that they have been instantiated.

## ASSUMED-UNVERIFIED

The bounded documentary source and literature screen does not establish
historical priority or exhaustive worldwide openness. The explicit unread
literature limits are retained in the source note.
