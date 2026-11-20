---
slug: jin-ning-xu-duan-2026-ferrers-rank-nine-example
bibkey: jinningxuduan2026ferrers
doi: null
url: https://arxiv.org/abs/2611.19070v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine
---

# The rank-nine Ferrers diagram example in Problem 1

## Problem

Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan ask the following in
*New constructions of optimal Ferrers diagram rank-metric codes for
quasi-block monotone Ferrers diagrams*, arXiv:2611.19070v1, §4, Problem 1,
on printed page 18 and PDF page 18.

> For example, does there exist an optimal Ferrers diagram rank-metric code for \(\mathcal{D}=\big[[2,3,4,4]\big]_{3}\) and \(d=9\) when \(q>3\) is an odd prime power?

[Problem 1, arXiv v1, PDF page 18](https://arxiv.org/pdf/2611.19070v1#page=18)

For every finite field $F$ of odd order $q>3$, the target is an $F$-linear
subspace of $12\times 12$ matrices of dimension 27. The top-aligned column
heights are $(6,6,6,9,9,9,12,12,12,12,12,12)$. Every codeword vanishes
below those heights, every nonzero codeword has rank at least nine, and a
nonzero codeword attains rank nine. Every supported linear code with
nonzero ranks at least nine has dimension at most 27.

## Motivation

The example asks whether the Ferrers bound is attained uniformly over the
specified field orders for a diagram with six full columns. It appears
in the source after the sufficient inequality in Proposition 3.12 fails
for the example's parameters. Example 3.5 treats the binary case.
[Paper, Example 3.5, PDF page 11](https://arxiv.org/pdf/2611.19070v1#page=11)

## Gap

Problem 1 also asks for constructions for a broader family beyond
Proposition 3.12. That family remains open in this development. The
settling declaration covers the displayed diagram, distance nine, and the
odd prime-power range stated in the example.
[Paper, Problem 1](https://arxiv.org/pdf/2611.19070v1#page=18)

## Route

Use subfields $K\subseteq L$ of degrees three and six over $F$ in a
degree-twelve field $E$. Order the tower basis so that the first six
output coordinates span $L$ and the first nine span $L+Kc$, where $c$ is
the third vector of the basis of $E$ over $K$. Choose linearized polynomials
whose evaluations on $K$ and $bK$ lie in these two spaces. Recovering the
parameters from the coefficient tuple and bounding the evaluation kernel
give an injective matrix map from $L^4\times K$, with nonzero ranks at
least nine. Projecting to the first three columns gives an attaining
word. Projecting to the first four columns gives the dimension bound
for every competitor.

## Falsifier

A field of an admissible order for which every supported code of
minimum rank at least nine has dimension at most 26 would refute the
example's existence assertion. A supported competitor of dimension
greater than 27 with nonzero ranks at least nine would refute the
formalized optimality assertion.

## Evidence

The frozen theorem
`D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine`
proves the exact example. Its Blueprint binds this dossier to that theorem.
The citation note records the support conventions and the literature comparison.
Five escape audit records remain open.
[Citation note](../Library/FiniteGeometry/jinningxuduan2026ferrers.md) ·
[Audit obligations](https://github.com/the-omega-institute/trureturing/issues/32088#issuecomment-7032750302)

## Triage

Theorem, tier 1. The fixed example asks for a uniform construction over
the stated field orders and has an attaining dimension and rank. The
preregistration states the field range and the dimension test.
[Issue #32088](https://github.com/the-omega-institute/trureturing/issues/32088)

## ASSUMED-UNVERIFIED

The bounded literature comparison leaves priority and indirect
reductions through other constructions unverified.
[Scope of the literature comparison](https://github.com/the-omega-institute/trureturing/issues/32088#issuecomment-7031226073)
