---
bibkey: tanzhang2026periodictilings
authors: Hu Tan, Ying Zhang
year: 2026
title: Periodic Tilings of Cardinality Twice a Prime or Nine in Arbitrary Dimension
doi: null
url: https://arxiv.org/html/2609.26576v1
claim: "Theorem 1.1 proves in every dimension that a tileable finite set of cardinality 2q for an odd prime q, or nine, has some fully periodic tiling complement, without a span restriction. It does not assert membership in each given tiling's orbit closure."
strata_touched:
  - D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry
  - D5/S1/Dynamics/Symbolic/KhetanSixCellPeriodicity
license: citation-only
triage: anchor
---

# Periodic-complement existence and the given-tiling distinction

## Verified locator

https://arxiv.org/html/2609.26576v1

Theorem 1.1; the twice-prime completion in §4.3; the covering-splitting
construction in §3.2; and the periodic replacement constructions in §5.3.

## Exact statement

Let $d\ge1$ and let $F\subset\mathbb Z^d$ be finite, with
$|F|=2q$ for an odd prime $q$, or $|F|=9$. If $F$ tiles by translations,
Theorem 1.1 asserts that there exist $M\ge1$ and
$B\subset\mathbb Z^d$ such that
$F\oplus B=\mathbb Z^d$ and $B+M\mathbb Z^d=B$.
There is no affine-span or intrinsic-rank restriction.

Taking $q=3$ covers every tileable six-point set. Thus existence of some
fully periodic six-cell complement is already a published preprint result
in this comparison and is not new here. Full periodicity of that $B$ is
stronger than a single period of $B$, but it does not assert that every
given complement $T$ is periodic or that $B$ lies in the orbit closure of
$1_T$. The construction permits replacement of the complement; its
statement carries no given-orbit-closure conclusion.

## Correspondence and limits of the comparison

`D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry.lean` follows the original
$T$ through its affine coordinate change and proves a period of that same
$T$ under two-direction cancellation. Its
`two_direction_orbit_closure_periodic` theorem gives a common period on
the actual orbit closure. The comparison is explained in
`Blueprint/D5/S1/Dynamics/Symbolic/KhetanLatticeGeometry.scribe.cs`.
The scoped-compiled full consumer `KhetanSixCellPeriodicity.lean` proves
a nonzero period of every given T, common to its whole orbit closure. Its
assumptions are exactly cardinality six, full integer difference span and
exact coverage. It thus retains the same given-tiling requirement as Khetan's pinned six-cell question, recorded in
[khetan2026nonconvex.md](khetan2026nonconvex.md).

The existence conclusion of Theorem 1.1 alone supplies no missing
orbit-closure bridge. This bounded comparison of the pinned statements is
not an exhaustive originality search and establishes no priority claim.
The bounded literature comparison is separate from the scoped Lean
verification; neither establishes official acceptance or completed
escape registration of the complete six-cell consumer.
