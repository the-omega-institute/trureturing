---
slug: dai-2026-cross-polytope-face-counts
bibkey: dai2026crosspolytopes
doi: null
url: https://arxiv.org/abs/2608.16037v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.full_cross_polytope_face_count
---

# Face counts for coordinate cross-polytope Minkowski sums

## Problem

Dai, Hou, Liu, Thawinrak and Wang, *Counting Lattice Points in Minkowski
Sums of Cross Polytopes*, arXiv:2608.16037v2, Problem 5.4, asks:

> Given their close connection to Minkowski sums of simplices, can one apply similar tools and techniques in [15] to study the faces of Minkowski sums of cross polytopes? In particular, can one give a formula for their f- and h-vectors (for those simple polytopes)?

Equation (3) specifies $Q=\sum_i\lambda_i\diamondsuit_{I_i}$ with
nonempty coordinate supports $I_i$ and nonnegative integer coefficients.
The face-count statement below extends the coefficients to nonnegative
reals. For arbitrary natural $n,m$, set
$A=\{i:\lambda_i>0\}$, $U=\bigcup_{i\in A}I_i$ and $d=|U|$.
For $0\le r\le d$, $f_r(Q)$ counts actual nonempty exposed faces of
actual affine dimension $r$, including the whole polytope. The empty-face
entry is separately $f_{-1}=1$.

## Motivation

The face formula is carried by
`D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.full_cross_polytope_face_count`.
Its left side is defined geometrically, independently of the formula.
The source is described in `Library/Geometry/dai2026crosspolytopes.md`.
The exact complete-family formula was registered before formal probes in
[issue 14604](https://github.com/the-omega-institute/trureturing/issues/14604).

## Gap

The source asks for face-enumeration tools for this family. The bounded
literature search in issue 14604 found the type A hypergraphic
correspondence of Benedetti, Bergeron and Machacek, Theorem 2.18, and
Thawinrak's wider type B face questions; neither provides this signed
coordinate formula by the tested direct correspondence. No exhaustive
literature or worldwide novelty claim follows from these readings.

## Route

Choose $J\subseteq A$, put $Z=\bigcup_{i\in J}I_i$ and $V=U\setminus Z$,
and choose $\varnothing\ne S_i\subseteq I_i\setminus Z$ for every
$i\in A\setminus J$. Set $S_i=\varnothing$ for all other indices and
$T=\bigcup_{i\in A\setminus J}S_i$. Form an undirected graph on **all**
of $V$ by joining distinct coordinates belonging to some common $S_i$.
Let $\mathcal C$ be its connected components and $c=|\mathcal C|$.
Put a strict arc $[a]\to[b]$ whenever $a\in(I_i\setminus S_i)\setminus Z$
and $b\in S_i$ for the same remaining summand. Retain only choices for
which this relation has no nonempty directed cycle, including self-loops.
Then the formula is

$$
f_r(Q)=\sum_{\substack{J,(S_i)\text{ feasible}\\d-c=r}}2^{|T|},
\qquad 0\le r\le d.
$$

A sign in $\{-1,1\}$ is chosen once per coordinate of $T$, shared across
all summands. A linear extension of the strict component order produces
one common exposing functional. Conversely an exposing functional
recovers feasible data, and equality of sum faces recovers their summand
faces because all active weights are positive. The actual direction
annihilator is the product of the coordinates outside $U$ and the equality
graph's real Laplacian kernel. Its dimension is $n-d+c$, so the actual face
dimension is $d-c$. Counting the resulting sign fibers gives the formula.

## Falsifier

The formula would fail if unselected isolated coordinates were discarded,
if strict self-loops were permitted, or if a shared coordinate received
independent signs in different summands. All three distinctions are
explicit in the definitions. The correspondence must count actual exposed
sets by actual affine-span dimension, rather than a proxy statistic.
No connectivity, generic-weight, distinct-support or full-dimensionality
assumption may be introduced.

## Evidence

The Lean source is
`D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.lean`; its explanatory
source is the matching Blueprint Scribe. The single full-family theorem
contains the forward realization, inverse classification, data/sign
injectivity, actual annihilator, actual dimension and finite fiber-count
arguments. It directly uses the repository's acyclic-reachability
antisymmetry theorem and pinned Mathlib's exposed-face, convex-hull,
graph-Laplacian and dual-dimension results. A formal proof establishes this
formula in the stated mathematical model; source fidelity and publication
are separate obligations.

## Triage

Tier 2; the target is the full-family face formula above. It has
`proof_shape: content` and `admission_basis: escape-witness` through its
dimension-preserving classification of actual faces. It is a general
mathematical theorem, rather than a bounded enumeration or a positive
finite instance.

The formula depends on the supports of positive-weight summands and on
which weights vanish; changing their positive magnitudes does not change
these face counts. Empty active sets yield the unique point face. Repeated
supports and disconnected configurations require no separate restriction.

For a relatively $d$-dimensional simple member, the ordinary transform gives

$$
h_Q(z)=\sum_{r=0}^d f_r(Q)z^{d-r}(1-z)^r
       =\sum_{J,(S_i)\text{ feasible}}2^{|T|}z^c(1-z)^{d-c}.
$$

This is an ordinary consequence on paper, not a separate Lean theorem.
It does not assert simplicity of every member or identify the Ehrhart
$h^*$-polynomial. The source's lattice-point results retain their original
hypotheses; no dependency of those results on Problem 5.4 is asserted.

## ASSUMED-UNVERIFIED

The simple-polytope $f$-to-$h$ transform is
not separately formalized here. A criterion for simplicity, general type B
face enumeration, and exhaustive literature priority remain outside this
statement.
