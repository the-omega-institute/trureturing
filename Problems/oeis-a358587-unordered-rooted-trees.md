---
slug: oeis-a358587-unordered-rooted-trees
bibkey: wisemanwu2024a358587
doi: null
url: https://oeis.org/A358587/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/UnorderedTrees/A358587.result
---

# Wu’s generating function and recurrence for A358587

## Problem

Let (a(n)) count isomorphism classes of unordered rooted trees on (n)
vertices whose vertex height equals their number of internal vertices.
The class at (n=0) is empty. Wu's generating function is
(x^5(x^2-x+1)/((x-1)^2(x+1)(2x-1)^2)), and the first seven terms are
(0,0,0,0,1,4,14). For every (n>7), the signed recurrence is
(a(n)=5a(n-1)-7a(n-2)-a(n-3)+8a(n-4)-4a(n-5)).
[OEIS A358587, revision 14](https://oeis.org/A358587/internal)

## Motivation

The identities require an all-size count on actual unordered rooted-tree
classes. The symmetry of the two equal arms is part of that count.
[Preregistration #34765](https://github.com/the-omega-institute/trureturing/issues/34765)

## Gap

The OEIS entry labels both formulas conjectural. The preregistered
literature search found related ranking and height-difference sequences.
It found no exact published proof in the sources it could inspect.
[Source screening](https://github.com/the-omega-institute/trureturing/issues/34765)

## Route

Pruning the original leaves produces a skeleton with one vertex outside
a longest path. That vertex and the path form a canonical rooted fork.
The original isomorphism classes correspond bijectively to decorations
by leaf multiplicities. Equal arms use the unique sorted pair
((m+1,m+d+1)), including equality at (d=0). Unequal arms have
independent positive tip counts. Stars and bars gives the coefficients
of the two decoration series. Clearing the denominator gives numerator
(x^5-x^6+x^7), and comparison above degree seven gives the recurrence.
The same count gives all seven initial values.

## Falsifier

An isomorphism class with zero or multiple normalized decorations, or an
index where the actual count violates either formula, would defeat the
corresponding claim.

## Evidence

The theorem quantifies over every natural index and uses the cardinality
of the qualifying classes of actual parent maps on `Fin n`.
[D5/S3/Combinatorics/UnorderedTrees/A358587.result](../D5/S3/Combinatorics/UnorderedTrees/A358587.lean)

## Triage

Tier 1 with open-problem-resolution admission. The proof uses the
size-preserving bijection and the resulting all-index count.

## ASSUMED-UNVERIFIED

Publication priority beyond the preregistered search remains unverified.
