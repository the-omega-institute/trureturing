---
slug: oeis-a358588-ordered-rooted-trees
bibkey: wisemanwu2024a358588
doi: null
url: https://oeis.org/A358588/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/OrderedTrees/A358588.result
---

# Wu’s generating function and recurrence for A358588

## Problem

Let a(n) count ordered rooted trees on n vertices whose vertex height equals
their number of nonleaf vertices. At index zero the class is empty. Wu’s
series is x⁵(−x² + x − 1)/((x − 1)³(x² − 3x + 1)²). The initial values at
indices one through seven are 0, 0, 0, 0, 1, 8, 41. For every n > 7 the
recurrence is a(n) = 9a(n−1) − 32a(n−2) + 58a(n−3) − 58a(n−4) +
32a(n−5) − 9a(n−6) + a(n−7). All arithmetic in the displayed identities is
over the integers. [OEIS A358588, revision 12](https://oeis.org/A358588/internal)

## Motivation

The formula block asks for an all-index connection between the actual
ordered-tree counts and the algebraic series and recurrence. The
preregistered claim preserves the node-height convention and the full
range of the published recurrence. [Issue #34741](https://github.com/the-omega-institute/trureturing/issues/34741)

## Gap

The source labels both formulas conjectural. Screening found generators
and a partial structural formalization. It found no published proof of
the full conjunction within the inspected sources.
[Source screening](https://github.com/the-omega-institute/trureturing/issues/34741#issuecomment-7210806435)

## Route

Prune the original leaves simultaneously. A valid tree leaves a
skeleton with one more vertex than its vertex height. The skeleton has
a unary stem and an ordered fork whose shorter arm has zero unary vertices.
For u unary vertices there are 2u+1 skeletons. The equal-arm case occurs
once. Each skeleton receives two mandatory terminal leaves and 2u+5
ordered free gaps. The gap counts sum to n−u−5 for an inflation of size n.
Weak composition cardinality gives the contribution at every size, and
its generating weight is (2u+1)x^(u+5)/(1−x)^(2u+5).

Summing these weights gives the quotient in the source. Simultaneously
negating its numerator and denominator yields a denominator with
constant coefficient one, so the quotient is defined in the formal
integer series ring. Comparing coefficients above degree seven gives
the recurrence. The actual count sum gives the three positive initial
values.

## Falsifier

Any actual tree missing from the reversible gap decomposition, a
duplicate in the ordered skeleton list, or any coefficient where the
resulting actual-tree count disagrees with Wu’s series would defeat the
stated argument.

## Evidence

The endpoint is
[D5/S3/Combinatorics/OrderedTrees/A358588.result](../D5/S3/Combinatorics/OrderedTrees/A358588.lean).
The theorem has an arbitrary natural index, a finite set cardinality,
the zero constant coefficient, the series equality, all seven initial
values and the recurrence in the integers under n > 7.

## Triage

Tier 1. The admission basis is open-problem-resolution. The proof uses
the reversible decomposition of actual ordered trees and the resulting
all-size binomial count on its live path to the series and recurrence.

## ASSUMED-UNVERIFIED

Publication priority beyond the cited source screening remains unverified.
