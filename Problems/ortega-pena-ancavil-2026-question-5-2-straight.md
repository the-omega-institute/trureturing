---
slug: ortega-pena-ancavil-2026-question-5-2-straight
bibkey: ortegapenaancavil2026hardsquare
doi: 10.48550/arXiv.2611.06780
url: https://arxiv.org/abs/2611.06780v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.result
---

# Ortega–Peña-Ancavil Question 5.2 for straight horizontal blocks

## Problem

Gabriel Ortega and Eliecer Peña-Ancavil ask whether Corollary 4.2 extends
to blocks of $k\ge 3$ sites and to blocks of arbitrary shape. This dossier
addresses straight horizontal blocks. The alphabet is all length-$k$ binary
words with no adjacent occupied bits. On a face $[a,b;c,d]$ the ordered
seams pair the last bit of $a$ with the first bit of $b$, and the last bit
of $c$ with the first bit of $d$. The vertical pairs are $(a,c)$ and
$(b,d)$, tested coordinatewise. Every tested pair forbids simultaneous
occupation. [Question 5.2](https://arxiv.org/html/2611.06780v1#S5.Thmtheorem2)

For any four nonzero complex numbers $A,B,C,D$, the target has value
$A^{|a|}B^{|b|}C^{|c|}D^{|d|}$ on supported faces and zero elsewhere. An
analytic family on a connected open complex domain uses this common face
support, is holomorphic in each variable, and satisfies (2.2) for every triple
with one nonzero scalar for all boundary assignments. The question is whether
the family can contain the target at an ordered parameter pair. [Definition 2.2](https://arxiv.org/html/2611.06780v1#S2.Thmtheorem2) · [Section 4.1](https://arxiv.org/html/2611.06780v1#S4.SS1)

## Motivation

The straight-block conclusion of Corollary 4.2 is formalized by
`D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction.result`.
[#31960](https://github.com/the-omega-institute/trureturing/issues/31960)

## Gap

The pinned source gives a certificate for length two. The larger alphabet
changes with $k$, so the straight-block clause requires a reduction that
covers every legal internal height at every width.

## Route

Take $0$ to be the empty height, $L$ to occupy even sites and $M$ to
occupy odd sites in one-based numbering. Use boundary $(0,M,L,L,0,L)$ in
(2.2). The left $P$ and $Q$ factors require $V(g,M)$ and $V(L,g)$,
which together force $g=0$. The right $P$ factor has vertical pair
$(L,L)$, with an occupied second site. The equation becomes

$$
P[L,0;0,M]\,Q[0,L;L,0]\,R[L,L;0,M]=0.
$$

All three faces are supported. In particular the seam $H(L,L)$ is
allowed because the first site of $L$ is empty, and $V(L,M)$ holds by
disjointness. At a special pair $(p,r)$ the middle entry is nonzero, so
varying $q$ gives a zero product of two holomorphic slices. The identity
theorem on the connected domain forces one slice to vanish there. The first
slice at $r$ and the third slice at $p$ are both nonzero target entries.

## Falsifier

A separately holomorphic common-support family satisfying the source
equation at every triple and containing the blocked target at any ordered
parameter pair would contradict the straight-block theorem.

## Evidence

The Lean definitions `Word`, `H`, `V`, `FaceSupport`, `Supported`, `blocked`,
`EqAt` and `HasFamily` encode the clauses above. The kernel proof uses
`AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero` from pinned Mathlib.
The Blueprint attaches one typed `OpenProblemResolutionClaim(Proved)` to
`result`. The uniform boundary reduction is the new mathematical step and
is used directly in the proof.

## Triage

The straight horizontal common-support clause has a nonexistence proof for
every $k\ge 3$. Arbitrary shapes, mixed support with row weights on $F$
and intertwiners on $F_V$, and Question 5.1 with hidden heights remain open
in this dossier.

## ASSUMED-UNVERIFIED

The bounded literature search in #31960 found no prior settlement in its
searched scope. Citation coverage and worldwide priority remain unverified.
