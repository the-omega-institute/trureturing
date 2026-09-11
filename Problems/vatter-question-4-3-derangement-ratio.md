---
slug: vatter-question-4-3-derangement-ratio
bibkey: vatter2026assortment
doi: null
url: https://arxiv.org/abs/2602.16355
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/DerangementRatioNonconvergence
---

# A negative answer to Vatter's Question 4.3

## Problem

Vincent Vatter, "An Assortment of Problems in Permutation Patterns: Unimodality,
Equivalence, Derangements, and Sorting", arXiv:2602.16355v2, Section 4:

> A permutation class is a downset (or order ideal) in this poset: a set 𝒞 of permutations such that if π∈𝒞 and σ≤π, then σ∈𝒞.

> For a permutation class 𝒞, let 𝒞° denote the set of derangements in 𝒞.

> Question 4.3. Does the ratio |𝒞°_n|/|𝒞_n| converge for every permutation class 𝒞?

## Motivation

This first-tier numbered question from a 2026 paper was selected in the
orchestrator's brief. The KPI is open problems resolved: the target is a
negative answer to the question as written, not a finite sample or a claim
about a restricted family of large classes.

## Gap

The orchestrator reported on 2026-09-08 that no answer was found in v1-v2 or
in identifier searches on arXiv, MathOverflow, and GitHub. This was a scoped
search, not an exhaustive literature review. This Stage-B seat had no network
access and did not independently repeat that search.

## Route

Take Av(12), the class of decreasing permutations. Pattern containment
preserves strict decrease, so this family is a downset. Each length slice is
the singleton {rev}. Reversal is a derangement if and only if the length n is
even. Thus the ratio at positive lengths is 0,1,0,1,...; Lean also includes
length zero, where the ratio is 1. The subsequences at 2k and 2k+1 are
constantly 1 and 0. Both index maps tend to infinity, so uniqueness of real
limits rules out convergence.

## Falsifier

A proof that the ratio converges for every permutation class under the quoted
definition, or an error in the downset proof of Av12, would falsify the proposed
resolution or its identification with the source question.

## Evidence

- Lean module: `D5/S1/Words/Patterns/DerangementRatioNonconvergence.lean`.
- Main theorems: `vatter_question_4_3_answer_no` and
  `exists_permClass_ratio_not_convergent`.
- Supporting theorems: `av12_mem_iff`, `card_av12`,
  `card_derangements_av12`, and `ratio_av12`; the parity criterion is
  `rev_isDerangement_iff`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the orchestrator's 2026-09-08 `#print axioms` check; Stage B did not rerun it.

## Triage

`theorem`. The question is answered in the negative by an explicit class.
This is a LITERAL refutation of the universally quantified question. The
author may have intended nontrivial or large classes; no assertion about
such an intended restriction follows from this counterexample.

## ASSUMED-UNVERIFIED

The verbatim quotes and definitions were supplied by the orchestrator from
the arXiv HTML. The pattern-containment definition used in Lean is the
standard order-embedding one: an increasing embedding of positions preserves
the relative order of values in both directions. A reader must check this
definition against the paper. The literature scope was the orchestrator's
2026-09-08 reading of v1-v2 and identifier searches on arXiv, MathOverflow,
and GitHub, not an exhaustive search; this seat had no network access.
First-publication priority and source-to-Lean fidelity are not kernel-checked
facts, and the author's possible intended restriction was not verified.
