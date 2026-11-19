---
slug: notik-real-golomb-minimizers
bibkey: notik2026singergolomb
doi: 10.48550/arXiv.2611.22656
url: https://arxiv.org/abs/2611.22656v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/RationalFarkas

---

# Notik's question on eight-, nine-, and ten-mark real Golomb rulers

## Problem

In §10, p. 8, third bullet, Esther Notik asks, “Uniqueness for n = 8, 9, 10: are the shortest real rulers again exactly the optimal integer rulers? The proofs of Theorem 1 give only the length.” Here uniqueness asks for equality of the two sets of minimizers, with both orientations included. [Paper, arXiv:2611.22656v1](https://arxiv.org/pdf/2611.22656v1#page=8)

For $x_1=0<x_2<\cdots<x_n$, write $d_{ij}=x_j-x_i$ for $i<j$. Require $d_{ij}\ge 1$ and $|d_{ij}-d_{kl}|\ge 1$ for distinct index pairs $(i,j)\ne(k,l)$. For each $(n,T)\in\{(8,34),(9,44),(10,55)\}$, an integral tuple attains $T$, every feasible real tuple has length at least $T$, and every feasible normalized tuple at length $T$ has integral coordinates. Strictly ordered integer rulers with distinct distances satisfy the real separation conditions, giving the reverse inclusion.

## Motivation

The minimum length alone leaves open whether equality can hold along a face containing nonintegral real rulers. The archive's lower-bound trees provide the active rows on each candidate equality face.

## Gap

Notik's Theorem 1 proves the lengths and gives witnesses. Theorem 2 classifies the equality cases through seven marks. The bounded literature screen in the Tier 2 preregistration found related occupancy relaxations, separated sumsets, and counting results, with no matching classification for the three larger real families. Recent, unpublished, and unindexed work were outside the verified coverage of that screen. [Preregistration #31427](https://github.com/the-omega-institute/trureturing/issues/31427)

## Route

Consecutive gaps give integer coefficients for every pair distance. For each real tuple one of its two orientations satisfies the initial branch convention. Established separation relations validate the signs in the tree and nonnegative integer weights certify the bound. At a tied leaf every positively weighted row is tight. The finite equality checker uses these rows to prove integral gaps directly or to rule out residual cases using separation and exact packing ranks. Reversing the gaps preserves integrality, and prefix sums recover the normalized marks.

## Falsifier

A feasible normalized real tuple at one of the three verified minimum lengths with any nonintegral coordinate would falsify the corresponding clause.

## Evidence

`D5/S3/Combinatorics/Golomb/NotikMinimizers.result` states all three sizes using the real carrier throughout and integer attainment at each target. The lower-bound replay and the equality replay use the same tree literals. The equality tables cover 349, 1,235, and 1,209 tied leaves, respectively. Lean checks the finite certificates and the soundness of their use on arbitrary real tuples. The translation of archive bytes and generation of equality certificates take place outside Lean. [Source citation](../Library/FiniteGeometry/notik2026singergolomb.md) · [Data attribution](../docs/reports/licenses/notik-golomb-archive.md)

## Triage

The equality cases are fixed by tight rows and the original separation relations. At each tied leaf the affine combinations, rank checks or residual exclusions force integral gaps. This argument addresses the six archived sizes through successive bounds and gives the equality classification at eight through ten marks.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources identified in #31427. Worldwide priority is unverified.
