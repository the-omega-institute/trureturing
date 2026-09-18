---
slug: centered-reduced-residue-progressions
bibkey: phothila2026centered
doi: 10.5281/zenodo.18154061
url: https://math.colgate.edu/~integers/aa6/aa6.pdf
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/CenteredReducedResidueProgressions.result
---

# Centered reduced residue progression maximum

## Problem

Let `n` be even and squarefree with at least three distinct prime factors. Let
`p` be its greatest prime factor and put `d=n/p`. Under `d<2p`, determine the
longest positive-step arithmetic progression in the fixed centered reduced
residue system from `-n/2+1` through `n/2`.

The unnumbered conjecture on printed page 14 of the cited paper states that the
maximum length is `floor(p-2p/d)`. The formal target expresses the maximum as
an `IsGreatest` statement, so it requires an attaining progression and a bound
for every positive step, together with the exact rational-floor equality.

## Motivation

The conjecture gives a closed formula for a maximum over all starts and all
positive steps in a source-fixed representative system. Its hypotheses couple
the distinct prime factors of a squarefree modulus to the geometry of the
centered interval.

## Gap

The cited paper presents the statement as a conjecture. The checked repository
and pinned Mathlib contain prime-factor, squarefree, modular, gcd, and floor
components, but no theorem with this centered progression maximum. The project
handoff at issue 7333 records the arithmetic route and releases it unclaimed;
issue 8677 identifies this exact source statement. These locators establish the
project provenance and do not support a priority claim.

## Route

Write `n=dp=2ep`. Squarefreeness and maximality give odd `e>=3`, prime `p>=5`,
and `gcd(d,p)=1`. A progression of the predicted length is obtained with step
`d` and start `p(2-e)+d`; endpoint inequalities follow from the nonzero
remainder of `2p` modulo `d`, and prime-divisor analysis proves every term is a
unit modulo `n`.

For an arbitrary positive step, if some prime factor of `d` is absent from the
step, a complete residue sweep supplies the upper bound. If the step is a
multiple `t*d` with `t>=2`, the centered interval diameter supplies it. For
step `d`, the unique centered multiple of `p` in the starting residue class
cannot be crossed; its two endpoint margins give the same bound. The positive
remainder then converts the natural quotient to `floor(p-2p/d)`.

## Falsifier

An even squarefree modulus in the stated domain with an admissible progression
longer than the formula, or with no progression attaining it, would refute the
maximum statement. A mismatch between the rational floor and the natural
quotient expression would refute the second conjunct.

## Evidence

The Lean module is
`D5/S3/ArithUnits/CenteredReducedResidueProgressions.lean`. Its `result`
theorem derives the complete factorization facts from the source hypotheses,
constructs the lower progression, proves the three exhaustive upper cases,
and proves the rational-floor identity without additional public assumptions.

## Triage

`theorem`; resolution kind `proved` for every modulus satisfying the literal
source domain. The calibration `n=30` is an instance of the theorem, not a
premise.

## ASSUMED-UNVERIFIED

Literature completeness outside the cited paper and the bounded searches is
unverified. No exhaustive novelty or publication-priority claim is made. The
source reading and project handoff locators are attributed evidence.
