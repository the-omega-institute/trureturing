---
slug: mohan-neetu-small-doubling-conjecture-61-refutation
bibkey: mohan2026smalldoubling
doi: 10.48550/arXiv.2607.11194
url: https://arxiv.org/abs/2607.11194v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result61
---

# Mohan-Neetu Conjecture 6.1

## Problem

Conjecture 6.1 in Mohan and Neetu, arXiv:2607.11194v1, section 6, asserts
that a nonempty finite subset S of a torsion-free group, partitioned into two
disjoint abelian sets A and B, generates an abelian subgroup whenever
`|S^2| <= 3k - 3`. Here `k = |S|`, `S^2 = {xy : x,y in S}`, and an abelian set
means one whose generated subgroup is abelian. The formal `claim61` quantifies
over the group and all three finite sets with these premises; `result61` proves
its negation.

## Motivation

The conjecture proposes a small-doubling threshold for the union of two
abelian pieces. Its conclusion is universal over torsion-free groups, so one
finite subset in such a group can refute it.

## Gap

The cited preprint prints this as a conjecture. The arXiv version listing and
scoped arXiv, Semantic Scholar, and Crossref searches recorded in issue #8686
found no subsequent settlement. The paper's Baumslag-Solitar theorems exclude
the parameter `q = -1`; the conjecture does not.

## Route

Use the Klein bottle group of pairs `(r,n)` with multiplication
`(r,n)(s,m) = (r + (-1)^n s,n+m)`. A positive power equal to the identity has
second coordinate zero only when `n = 0`; its first coordinate then vanishes
only when `r = 0`. Thus this group is torsion-free.

Take `S = {(0,0),(0,1),(1,1)}`, `A = {(0,0),(0,1)}` and `B = {(1,1)}`.
The pieces are disjoint and generate abelian subgroups. The six distinct
products of S satisfy `|S^2| = 6 = 3|S| - 3`, but
`(0,1)(1,1) = (-1,2) != (1,2) = (1,1)(0,1)`.

## Falsifier

The refutation would fail if the coordinate group had a nonidentity element
of finite order, either piece generated a nonabelian subgroup, the product set
had more than six elements, or the displayed pair commuted. Each fact is a
proof obligation of `result61`.

## Evidence

`D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result61` is a
Lean theorem of type `not claim61`. Its proof establishes torsion freeness by
power-coordinate induction and checks the finite products and noncommutation
in the pinned toolchain. Its axiom closure is `propext`, `Classical.choice`,
and `Quot.sound`.

## Triage

`theorem`. This refutes the printed Conjecture 6.1, with `k = |S|`; it does
not assert a replacement doubling threshold.

## ASSUMED-UNVERIFIED

The scoped literature search does not establish exhaustive publication
priority. Google Scholar and the full texts of the arXiv Klein-bottle search
hits were not checked.
