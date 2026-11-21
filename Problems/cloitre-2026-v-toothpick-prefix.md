---
slug: cloitre-2026-v-toothpick-prefix
bibkey: cloitre2026vtoothpick
doi: null
url: https://arxiv.org/html/2611.23172v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.honeycombGraph
---

# Cloitre's V-toothpick prefix corrections

## Problem

[Section 9](https://arxiv.org/html/2611.23172v1#S9.p3), p. 30, asks:

> It is unknown whether all prefix corrections ηⱼ vanish, or equivalently whether, for every dyadic P, the coefficients of E_c of degree less than P are determined by c modulo 2P.

For integer degree $j≥1$ and integer column $0≤c≤j−2$, put $p_j=2^{⌊log₂ j⌋+2}$ and
$e_j(c)=[z^j]E_c(z)$. With Euclidean remainder in the signed offset, define
$π_j(r)=e_j(j−1+((r−j+1)\bmod p_j))$. The target is
$e_j(c)=e_j(c+p_j)=π_j(c\bmod p_j)$ and $η_j(c)=0$.

## Motivation

The finite growth uses the literal honeycomb graph with the three A-to-B
neighbor offsets. Vanishing extends the periodic readout to the full prefix
range of the author's question. [Preregistered statement](https://github.com/the-omega-institute/trureturing/issues/32146)

## Gap

Theorem 39 gives the eventual range $c≥j−1$. The finite checks in
Appendix B, Proposition 43 cover degrees through 63.

## Route

For dyadic (P>j), compare height (4P) at column (c+2P) with height
(3P) at column (c). For both adjacent cuts the strict diagonal cut bound
is the same. Signed support puts every contributing vertex below its
first-touch horizon. The matching signed coefficients combine with the
dyadic copy identity and the enclosure-independent readout of equation (17).
The least eligible (P) gives the period and the Euclidean index in
equation (43).

## Falsifier

One eligible pair (j,c) with unequal exact coefficients at (c) and
(c+p_j) falsifies the equality.

## Evidence

The theorems use synchronous first touch on the repository honeycomb and the
integer signed birth-count polynomials. [Displaced-wall proof](https://github.com/the-omega-institute/trureturing/issues/32152#issuecomment-7034791579)

## Triage

The signed weights need only agree below the displaced-wall horizon, since
the coefficient reads carry no contributions outside it. The shared
coefficient is allowed to be nonzero. The degree (j=1) admits no prefix
column.

## ASSUMED-UNVERIFIED

The cited preprint records that the universal prefix question is open.
Literature completeness and worldwide priority remain unverified.
