---
slug: zhao-vincular-stack-three-sorting-classes
bibkey: zhao2024vincular
doi: 10.1016/j.disc.2025.114834
url: https://arxiv.org/abs/2410.17057v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/VincularStack/VincularStackThree.result
---

# Equal Sorting Classes and Outputs of the Stacks Avoiding 312, 31-2 and 3-12

## Problem

Zhao, arXiv:2410.17057v1, Conjecture 5.1 (Section 5, printed page 20):

> The sorting classes of SC_{312} and SC_{31̲2} are identical. That is, Sort_n(SC_{312}) = Sort_n(SC_{31̲2}) =
> Sort_n(SC_{31̲2̲}). Furthermore, for τ ∈ Sort_n(SC_{312}), we have SC_{312}(τ) = SC_{31̲2}(τ) = SC_{31̲2̲}(τ).

SC_σ is the right-greedy stack map whose stack, read from top to bottom, must avoid σ; σ is the classical
pattern 312, the vincular pattern in which the entries playing 3 and 1 are adjacent, or the vincular pattern in
which the entries playing 1 and 2 are adjacent. Sort_n(SC_σ) is the set of permutations of length n whose image
avoids 231.

## Motivation

The theorem `D5/S3/Combinatorics/VincularStack/VincularStackThree.result` establishes the statement: for every
n ≥ 1 the three sorting classes are equal, and the three stack maps agree on every permutation of the class.

## Gap

Pre-registration issue 12193 records the literature screen: the only work citing arXiv:2410.17057 concerns the
fully consecutive pattern, and the arXiv, OEIS and GitHub searches located no treatment of this conjecture.
This is a bounded negative finding.

## Route

1. Avoidance of the classical pattern and of the two vincular patterns coincide on stacks that are maintained
   by the machines, so the three machines run identically until the first push that one of them refuses and
   another accepts.
2. At the first such disagreement the state has a normal form that forces an occurrence of 231 in the output of
   every machine, so a disagreeing input is unsortable for all three.
3. Hence on a sortable input the three runs coincide step by step, which gives equal sorting classes and equal
   outputs.

## Falsifier

The statement would fail if some input were sortable for one machine while the three runs disagreed, that is,
if a first disagreement did not force 231 in every output.

## Evidence

The three classes and the three outputs on the class were checked on all permutations of length at most 11;
the class sizes 1, 2, 5, 15, 52, 201, 843, 3764, 17659 for n ≤ 9 agree with Table 2 of the source.

## Triage

`theorem`; the statement is Conjecture 5.1 of arXiv:2410.17057 and is quantified over every n ≥ 1.

- Proved (formalized): the classical machine and the machine whose 3 and 1 must be adjacent agree on every
  permutation, sortable or not, because the two avoidance conditions coincide on the stacks they maintain. Only
  the machine whose 1 and 2 must be adjacent can diverge, and every divergence is fatal for all three.
- Proved (paper proof, not formalized): a sortable state's stack consists of consecutive intervals, and the
  admissible next letters are described exactly; this gives a generating tree with tuple labels and an exact
  recurrence for the common class size, whose values for n ≤ 10 are 1, 2, 5, 15, 52, 201, 843, 3764, 17659,
  86245.
- Open: a closed form or algebraic generating function for the class size. The source lists the enumeration of
  Sort_n(SC_{312}) as left open by Cerbai, Claesson and Ferrari; the tuple-label recurrence does not settle it,
  and the agreement of the first nine terms with OEIS A202062 is not proved for all n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation index, arXiv, OEIS and GitHub searches and the repository
checks recorded above; the journal version was not read in full.
