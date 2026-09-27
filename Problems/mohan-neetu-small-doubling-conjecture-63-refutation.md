---
slug: mohan-neetu-small-doubling-conjecture-63-refutation
bibkey: mohan2026smalldoubling
doi: 10.48550/arXiv.2607.11194
url: https://arxiv.org/abs/2607.11194v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result63
---

# Mohan-Neetu Conjecture 6.3

## Problem

Conjecture 6.3 in Mohan and Neetu, arXiv:2607.11194v1, section 6, asserts
that a finite subset S of a torsion-free group with `|S| >= 3`, identity in
S, and `|S^2| <= 3|S| - 3` generates an abelian subgroup. The formal
`claim63` states these quantified premises and conclusion; `result63`
proves `not claim63`.

## Motivation

The paper exhibits a nonabelian small-doubling set without the identity and
proposes identity membership as a sufficient additional hypothesis. An
identity-containing counterexample tests precisely that addition.

## Gap

The cited preprint prints this as a conjecture. The arXiv version listing and
scoped arXiv, Semantic Scholar, and Crossref searches recorded in issue #8686
found no subsequent settlement. The conjecture quantifies over every
torsion-free group, including the Klein bottle group.

## Route

Use the torsion-free Klein bottle group of integer pairs with multiplication
`(r,n)(s,m) = (r + (-1)^n s,n+m)`. Its torsion-freeness follows from the
second coordinate of a positive power and then the first coordinate at
`n = 0`. Take `S = {(0,0),(0,1),(1,1)}`. Its product set is
`{(-1,2),(0,0),(0,1),(0,2),(1,1),(1,2)}`. Thus `|S| = 3`, the identity
is in S, and `|S^2| = 6 = 3|S| - 3`. However,
`(0,1)(1,1) = (-1,2) != (1,2) = (1,1)(0,1)`.

## Falsifier

The refutation would fail if the coordinate group had torsion, the listed
set omitted the identity, its product set had more than six elements, or the
displayed pair commuted. All four are settled in `result63`.

## Evidence

`D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result63` has
Lean type `not claim63`. The proof uses the coordinate torsion-freeness
lemma and checks the finite set and unequal products in the pinned toolchain.
Its axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. This refutes the identity-containing Conjecture 6.3; it does not
claim a corrected threshold or classify all extremal subsets.

## ASSUMED-UNVERIFIED

The scoped literature search does not establish exhaustive publication
priority. Google Scholar and the full texts of the arXiv Klein-bottle search
hits were not checked.
