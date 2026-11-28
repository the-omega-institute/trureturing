---
slug: mekera-somer-yesil-nilpotent-adjacency
bibkey: mekerasomeryesil2026annihilatordigraphs
doi: 10.48550/arXiv.2608.09243
url: https://arxiv.org/html/2608.09243v2#S7.p2.1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.result
---

# Distinct nonzero nilpotents can be nonadjacent

## Problem

Mekera, Somer and Yeşil ask in §7 whether two distinct nonzero nilpotent
elements of a noncommutative ring are necessarily adjacent in its
annihilator digraph. The claim ranges over associative rings with
noncommutative multiplication and allows rings without identity. For every
pair of distinct nonzero elements each killed by some positive power, it
asks for an arc in at least one direction.
[Versioned question](https://arxiv.org/html/2608.09243v2#S7.p2.1)

## Motivation

A nonzero nilpotent element is a vertex because its last nonzero power is a
nonzero annihilator. The arc relation asks for an annihilator of an ordered
product that avoids the annihilators of both endpoints on the same side.
[Definitions](https://arxiv.org/html/2608.09243v2#S4.Thmtheorem1)

## Gap

For distinct vertices $x,y$, a left witness must satisfy $t(xy)=0$,
$tx\ne 0$ and $ty\ne 0$. A right witness must satisfy $(xy)t=0$,
$xt\ne 0$ and $yt\ne 0$. The reverse arc uses $yx$ with its own witnesses.
Both witness alternatives must fail for each product order.

## Route

In $M_2(\mathbb F_2)$ take $A=E_{12}$ and $B=E_{21}$. Both are distinct
nonzero square-zero matrices. The diagonal products $AB=E_{11}$ and
$BA=E_{22}$ differ, so the ambient ring is noncommutative. The square-zero
identities also certify vertex membership using each element itself.

## Falsifier

The identities $(AB)A=A$, $B(AB)=B$, $(BA)B=B$ and $A(BA)=A$ imply
respectively that $t(AB)=0$ forces $tA=0$, $(AB)t=0$ forces $Bt=0$,
$t(BA)=0$ forces $tB=0$, and $(BA)t=0$ forces $At=0$. Each equality
contradicts one of the endpoint requirements for that witness.

## Evidence

Lean proves the literal negation of the universal claim for carriers in
Type 0. The proof lifts the binary coefficient type to refute the same
assertion at each universe. Nilpotence uses the positive power indexed by
$k$, with $k=1$ giving the square.
[Lean result](../D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.lean) ·
[Literature note](../Library/Certificates/mekerasomeryesil2026annihilatordigraphs.md) ·
[Problem #35242](https://github.com/the-omega-institute/trureturing/issues/35242)

## Triage

The same matrix-unit identities yield counterexamples over every field in
each finite dimension at least two. The Lean model uses binary
coefficients in dimension two.

## ASSUMED-UNVERIFIED

The accessible literature search found no earlier settlement of the
versioned question under Definition 4.1. Search completeness and worldwide
priority remain unverified.
[Search scope and limitations](https://github.com/the-omega-institute/trureturing/issues/35242)
