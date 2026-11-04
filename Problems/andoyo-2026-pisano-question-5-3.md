---
slug: andoyo-2026-pisano-question-5-3
bibkey: andoyo2026pisanolegendrecollision
doi: 10.62072/acm.2026.09011
url: https://arxiv.org/html/2601.10561v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/AndoyoPisanoSetCollision.result
---

# Andoyo's equal Pisano sets question

## Problem

Section 5, Question 5.3 asks:

> Are there values of a₁, a₂, b₁, and b₂ for which χ(a₁,b₁)=χ(a₂,b₂)?

The preceding paragraph requires a₁,b₁,a₂,b₂∈ℤ, distinct ordered pairs,
and neither pair equal to (0,0). Definitions 2.6 and 2.7 specify the least
positive scalar period at every nonnegative index, the three index counts
for Legendre values 1,−1,0, and their integer difference over all odd primes.

## Motivation

The frozen declaration `D5/S3/Arith/AndoyoPisanoSetCollision.result`
answers the existential question affirmatively with the distinct nonzero
integer seed pairs (0,1) and (1,1). Their complete Pisano sets agree over
all odd primes, with the source's least positive scalar periods and all
three Legendre index counts.

## Gap

Preregistration: [#22843](https://github.com/the-omega-institute/trureturing/issues/22843).
The bounded named source screen in the
[implementation assignment](https://github.com/the-omega-institute/trureturing/issues/22843#issuecomment-6452213455)
reports no exact settlement within its stated readings. The versioned preprint
and journal text both explicitly pose Question 5.3. Broader web, citation,
code and Reservoir coverage remains unmeasured; no global absence or
publication priority claim follows.

## Route

Write fₙ=Fₙ(0,1)
and gₙ=Fₙ(1,1). Their recurrences give gₙ=fₙ₊₁. Every positive scalar
period of f is one of g. Conversely, a scalar period t of g gives
fₜ₊₁≡f₁ and fₜ₊₂≡f₂; the recurrence gives fₜ≡f₀, including the missing
zeroth index. The remaining indices follow by shifting. Thus the complete
sets of positive scalar periods agree, and so do their least members.

Existence of a positive period follows from the invertible Fibonacci step
on the finite pair space over ZMod p, using the original canonical
`PisanoMatrixBridge.period_iff_return`. No common-period replacement is used.

Let T be the shared least period. For any of the three Legendre classes,
write uₙ for its zero-or-one index indicator. Periodicity gives uT=u0, and
the two decompositions of the sum over 0,…,T give

\[
\sum_{n=0}^{T-1}u_{n+1}+u_0
=\sum_{n=0}^{T-1}u_n+u_T.
\]

Cancellation proves equality of the two index counts. This includes the
zero class and the wraparound endpoint and uses no T>1 assumption.
The three equalities give equal K values for each same prime, hence equal
sets over all odd primes.

## Falsifier

The source correspondence would fail if the source excluded either witness,
identified shifted seed pairs, or used a different period or counting convention.
The proof mechanism would fail if reverse period transport omitted index zero,
or if any Legendre-class count changed at the wraparound endpoint. The statement
echo and the period and count equalities address these obligations for the
literal integer-seed question; finite prime samples cannot establish it.

## Evidence

The source is Definitions 2.6 and 2.7 and Section 5, Question 5.3 in the
[versioned preprint](https://arxiv.org/html/2601.10561v1) and
[journal text](https://www.technoskypub.com/wp-content/uploads/2026/04/acm-090111.pdf),
identified by `andoyo2026pisanolegendrecollision` and DOI `10.62072/acm.2026.09011`.
The clause correspondence is:

| Source clause | Lean counterpart |
| --- | --- |
| Integer initial values and recurrence from n=0 | `F (a b : ℤ)`, with branches `0`, `1`, and `n+2` |
| Positive scalar period for every n≥0 modulo p | `ScalarPeriod p a b t` |
| Least such positive period | `pi`; `least_period` proves positive membership and minimality for (0,1); `pi_equal` proves the same minimum for (1,1) using both directions of `periods_equal` |
| All indices 0,…,π−1, with repeated values counted repeatedly | `signCount` is the cardinality of a filtered `Finset.range` of indices |
| Legendre classes 1,−1,0 | The three arguments of `signCount` in `K` |
| Integer subtraction | Each count is cast to ℤ separately in `K` |
| All odd primes | `chi` quantifies over every natural prime p with p≠2 |
| Distinct nonzero ordered seed pairs | The three inequalities in `result`, witnessed by (0,1) and (1,1) |
| Equality of complete Pisano sets | The final equality in `result` |

## Triage

Theorem: the established collision follows from cyclic phase invariance of
index counts over the shared least period, including the zero class. It is an
existence result for (0,1) and (1,1), not a classification of all collisions.
The neighboring research candidate is the source's
[Question 5.2](https://arxiv.org/html/2601.10561v1#S5.Thmquestion2): for integers
a,b with (a,b)≠(0,0), does every k∈χ(a,b) satisfy
|ϑ_(a,b)(k)|=ℵ₀? It asks for infinitely many odd primes at each attained
balance; the collision theorem supplies no such infinitude or distribution
result. [PR #22894](https://github.com/the-omega-institute/trureturing/pull/22894)
is published; merge and delivery remain pending.

## ASSUMED-UNVERIFIED

The literature absence is bounded to the source screen described above.
The information-escape audit remains unfinished as disclosed in
[#22843](https://github.com/the-omega-institute/trureturing/issues/22843#issuecomment-6452874717);
the issue is not completed registration evidence. Classification of other
seed-pair collisions and the neighboring Question 5.2 are outside the proved
result. This dossier makes no world-priority claim.
