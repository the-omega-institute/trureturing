---
slug: barket-central-quotient-eigengap-conjecture-refutation
bibkey: barket2026graphical
doi: 10.48550/arXiv.2607.12026
url: https://arxiv.org/abs/2607.12026v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BarketCayleyEigengapRefutation.result
---

# Refutation of the central-quotient eigengap conjecture

## Problem

Barket, Grimaldi, Hendi, Hirst, Onus, and Singh, *Learning the Graphical
Nature of Symmetries*, arXiv:2607.12026v1, Conjecture 4.4, assert that for a
finite nilpotent group `G` and a generating set `S`, the first consecutive
normalised-Laplacian eigengap greater than one has index either `|G| - 1` or
`|G / Z_j(G)|` for some `1 <= j <= c`, where `c` is the nilpotency class.

The formal claim includes the source condition that this first eigengap is
defined and uses the underlying undirected multiplicative Cayley graph.

## Motivation

The cyclic group of order five with generator one gives a finite exact test
case. Its Cayley graph is the 5-cycle, whose spectrum makes the first gap
above one occur at an index outside both alternatives in the conjecture.

## Gap

The result refutes the literal statement in arXiv version 1. It does not
propose a corrected spectral characterization or make a priority claim.

## Route

For `G = Z/5` and `S = {1}`, the normalised Laplacian has characteristic
polynomial

`X (X^2 - (5/2) X + 5/4)^2`.

Its ascending spectrum is `[0, a, a, b, b]`, where
`a = (5 - sqrt(5))/4` and `b = (5 + sqrt(5))/4`. The consecutive gaps are
`[a, 0, sqrt(5)/2, 0]`, so the first gap greater than one has index three.
The group has nilpotency class one, the final index is four, and its only
admissible central quotient has cardinality one. Thus neither alternative
equals three.

## Falsifier

A proof of the published universal claim would specialize to the cyclic
group of order five and generator one. The frozen theorem
`D5/S3/Combinatorics/BarketCayleyEigengapRefutation.result` proves the
negation of that claim using this instance.

## Evidence

- Lean module:
  `D5/S3/Combinatorics/BarketCayleyEigengapRefutation.lean`.
- Main theorem: `result : Not claim`.
- The characteristic polynomial and sorted spectrum are derived exactly;
  the proof uses no floating-point approximation and no `native_decide`.
- Literature source: DOI `10.48550/arXiv.2607.12026`, version 1.

## Triage

`theorem`. The certified instance refutes the literal universal statement.
The proof shape is `bind-only`, the admission basis is
`open-problem-resolution`, and the utility basis is the typed `refutes` edge
from `result` to `claim`.

## ASSUMED-UNVERIFIED

The literature check is bounded to the cited arXiv version and the recorded
repository search surfaces. Exhaustive publication coverage and priority
were not verified and are not claimed.
