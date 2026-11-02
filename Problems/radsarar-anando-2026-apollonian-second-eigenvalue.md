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
The [source note](../Library/Eigenstructure/radsararanando2026apollonian.md)
attributes the quotation and adapted exposition to the author under CC BY-SA 4.0.

## Motivation

The dominant old vertices have exponentially growing degree, while their
common late neighbours grow only linearly. A fixed old cutoff exposes this
separation through the Gram matrix of the old-to-late adjacency block.

## Gap

The exact all-stage spectral limit is **Proved** by
`D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit.result : InnerFaceStages.limitClaim`.
It quantifies along every natural stage, including odd stages, without an
additional degree or spectral hypothesis. This is the formal completion of
the accepted ordinary proof attributed in the source note, rather than a
claim to a new ordinary solution or worldwide priority.
The forward preregistration is
[issue #24989, comment 6550398124](https://github.com/the-omega-institute/trureturing/issues/24989#issuecomment-6550398124).
It retains unit 24989, cutoff `2026-11-01T11:00:00Z` and `predictions: []`;
the earlier unit 24905 settlement is unchanged.

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
The exact proposition proved by
[SecondEigenvalueLimit.result](../D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit.lean)
is `InnerFaceStages.limitClaim`;
`secondEigenvalue` uses the decreasing real ordinary-adjacency spectrum,
with index one and multiplicities, and the normalization is a real power.
`cutoffEquiv` is the exact old/late vertex bijection, and `cutoff_adjacency`
identifies every entry with the corresponding ordinary adjacency block.
The final result combines these combinatorial statements with the spectral
and analytic interfaces below.
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
The final proof identifies the limiting second Gram eigenvalue as two,
proves eventual positivity, transports the cutoff spectrum with its
multiplicities, and controls the actual full adjacency remainder. Its
[canonical exposition](../Blueprint/D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit.md)
records the `Proved` source-resolution claim.

The [unfinished registration audit](https://github.com/the-omega-institute/trureturing/issues/24989#issuecomment-6554047951)
remains separate from mathematical proof under CLAUDE.md section 3.9.
There are 27 public targets: 21 retained records, comprising eight validated
and thirteen unfinished records, plus six faithful failed attempts with no
retained source. No target lacks an attempt; nineteen lack a completed
registration. The thirteen retained gaps are nine `InnerFaceStages` records
(three `source.observation_data`, six `source.params`),
`CutoffGramLimit.normalized_gram_tendsto`, both public
`CutoffSpectralBounds` bounds and `SecondEigenvalueLimit.result`
(four `source.selection_missing` in total). These retain `IE-C050` and no
certificate. The three `source.observation_data` targets are
`InnerFaceStages.adjacent_embed`, `inner_faces_distinct` and
`late_edge_oriented`; the six `source.params` targets are
`cutoff_adjacency`, `cutoff_gram_diag`, `cutoff_gram_offdiag`,
`degreeCount_late_le`, `late_oriented_indegree_le` and `old_vertices_iff`.
The six failed targets are `InnerFaceStages.faceCount_new`,
the B-hosted Schur norm theorem, `RectangularDilation.eigenvalues_ofReal`,
both unequal-dilation identities and the cutoff ordered-spectrum identity.
Their respective readings are failure of observational dependence for the
constant-three count, absence of the `RCLike (ULift Real)` negative witness,
`contract.discovery:rigid_universes`, lifted finite-matrix transparency
failure for both unequal identities, and absence of a compiled finite
second-Gram positivity witness. Existing valid sources and binding evidence
remain in place; the resolution claim does not assert complete registration.

## Triage

- **Proved:** the centre has limiting Gram weight three, the three outer
  seeds have weight two, and every other weight is at most two. Thus the
  second decreasing limiting eigenvalue is exactly two, with multiplicity.
- **Proved:** fixed-cutoff Gram convergence gives convergence of its ordered
  second eigenvalue and eventual positivity. The unequal-block dilation
  identity then yields the cutoff second-eigenvalue limit $\sqrt2$.
- **Proved:** exact vertex transport decomposes the adjacency error into
  the fixed old block and the actual late induced block. After normalization,
  the former tends to zero with the stage and the latter is bounded by
  $3\sqrt2/2^{k/2}$. Choosing the cutoff first and then the stage proves the
  full natural-stage limit, including odd stages. The graph bounds are
  consequences of the construction, not supplied spectral assumptions.
- **Unresolved adjacent questions:** limits for further leading eigenvalues,
  rates of convergence, and variants using other face conventions or
  operators are not settled by this theorem. The fixed-cutoff method gives
  a route to examine them, but the necessary limiting weights, ordered
  positive-prefix conditions and remainder estimates must be checked for
  each target. No new such theorem is asserted here.
- **Source scope:** this resolves the stated second-eigenvalue question at
  the mathematical level by formalizing the attributed ordinary argument.
  The source's broader question about other leading eigenvalues remains
  outside this result. The nineteen unfinished registration targets remain
  audit obligations under the linked issue.

## ASSUMED-UNVERIFIED

The bounded documentary source and literature screen does not establish
historical priority or exhaustive worldwide openness. The explicit unread
literature limits are retained in the source note.
