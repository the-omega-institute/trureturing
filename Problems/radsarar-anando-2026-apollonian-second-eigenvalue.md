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

The all-stage spectral limit remains to be composed from the actual cutoff
norm, Gram convergence and ordered-spectrum identities.
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
The exact unproved proposition is `InnerFaceStages.limitClaim`;
`secondEigenvalue` uses the decreasing real ordinary-adjacency spectrum,
with index one and multiplicities, and the normalization is a real power.
`cutoffEquiv` is the exact old/late vertex bijection, and `cutoff_adjacency`
identifies every entry with the corresponding ordinary adjacency block.
These combinatorial statements alone do not establish the spectral limit.
The actual late adjacency norm interface belongs to
[CutoffSpectralBounds](../D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.lean).
Its bound uses the proved birth orientation and the finite Schur operator bound.
For every cutoff $k$ and later increment $t\ge1$, it gives
$\|C\|/2^{(k+t)/2}\le3\sqrt2/2^{k/2}$ with real exponents, including odd stages.
The fixed-cutoff matrix convergence belongs to
[CutoffGramLimit](../D5/S3/Combinatorics/Apollonian/CutoffGramLimit.lean):
$2^{-(k+t)}BB^\top$ tends to the diagonal with weights
$\operatorname{faceCount}(k,u)/2^k$ on the fixed actual vertex set.
The real unequal-block identity belongs to
[CutoffOrderedSpectrum](../D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.lean).
It identifies the second decreasing eigenvalue of $[[0,B],[B^\top,0]]$
with the square root of the second Gram eigenvalue when the latter is positive.
The positive prefix retains signs, zero padding and algebraic multiplicities;
the old and late vertex sets need not have equal sizes.
The [unfinished graph registrations](https://github.com/the-omega-institute/trureturing/issues/24989#issuecomment-6552933239)
remain separate from mathematical compilation, under the linked-issue route.
The additional spectral registration obligations are tracked under
[the same issue](https://github.com/the-omega-institute/trureturing/issues/24989).
No frozen graph-specific spectral resolution is asserted here.

## Triage

The remaining mathematical steps are to identify the limiting diagonal's
second decreasing eigenvalue as $2$, transfer the fixed-cutoff matrix limit
to second-eigenvalue convergence and eventual positivity, apply the existing
scaling and perturbation results to the actual full adjacency decomposition,
and compose the limits in the order $t\to\infty$ followed by $k\to\infty$.
The result must cover all natural stages with the original real-power
normalization. Existing generic perturbation and scaling declarations remain
suppliers for this composition.

## ASSUMED-UNVERIFIED

The bounded documentary source and literature screen does not establish
historical priority or exhaustive worldwide openness. The explicit unread
literature limits are retained in the source note.
