---
slug: mohan-neetu-small-doubling-conjecture-62-refutation
bibkey: mohan2026smalldoubling
doi: 10.48550/arXiv.2607.11194
url: https://arxiv.org/abs/2607.11194v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result62
---

# Mohan-Neetu Conjecture 6.2

## Problem

Conjecture 6.2 in Mohan and Neetu, arXiv:2607.11194v1, section 6, asserts
that a nonempty finite subset S of a torsion-free group, partitioned into
three pairwise disjoint abelian sets A, B and C, generates an abelian subgroup
when `|S^2| <= 3k - 4`. Here `k = |S|`, `S^2` is the product set, and an
abelian set has an abelian generated subgroup. The formal `claim62` retains
every premise; `result62` proves its negation.

## Motivation

The authors' Example 6.1 shows that a weaker three-piece threshold fails.
Conjecture 6.2 asks whether lowering that threshold by one restores
commutativity.

## Gap

The cited preprint prints this as a conjecture. The arXiv version listing and
scoped arXiv, Semantic Scholar, and Crossref searches recorded in issue #8686
found no subsequent settlement. Its universal hypothesis does not exclude
the Klein bottle group.

## Route

In the torsion-free Klein bottle group `(r,n)(s,m) =
(r + (-1)^n s,n+m)`, let `S = {(1,1),(2,1),(3,1)}` and take its three
singleton subsets as A, B and C. Singleton-generated subgroups are abelian
and the pieces are pairwise disjoint. The product set is
`{(-2,2),(-1,2),(0,2),(1,2),(2,2)}`, so `|S^2| = 5 = 3|S| - 4`.
Yet `(1,1)(2,1) = (-1,2) != (1,2) = (2,1)(1,1)`.

## Falsifier

The refutation would fail if the coordinate group had torsion, the singleton
pieces were not pairwise disjoint and abelian, the displayed product set had
more than five elements, or the pair commuted. `result62` discharges these
conditions.

## Evidence

`D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result62` has
Lean type `not claim62`. Its proof uses the coordinate torsion-freeness lemma,
subgroup closure of singletons, and checked finite products. Its axiom closure
is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The conclusion refutes Conjecture 6.2 as printed; the stronger
threshold and any proposed correction remain outside the claim.

## ASSUMED-UNVERIFIED

The scoped literature search does not establish exhaustive publication
priority. Google Scholar and the full texts of the arXiv Klein-bottle search
hits were not checked.
