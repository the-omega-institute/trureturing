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

Preregistration: [#22843](https://github.com/the-omega-institute/trureturing/issues/22843).
The fixed Stage A assignment is the linked issue's
[implementation assignment](https://github.com/the-omega-institute/trureturing/issues/22843#issuecomment-6452213455).
Section 5, Question 5.3 asks:

> Are there values of a₁, a₂, b₁, and b₂ for which χ(a₁,b₁)=χ(a₂,b₂)?

The preceding paragraph requires a₁,b₁,a₂,b₂∈ℤ, distinct ordered pairs,
and neither pair equal to (0,0). Definitions 2.6 and 2.7 specify the least
positive scalar period at every nonnegative index, the three index counts
for Legendre values 1,−1,0, and their integer difference over all odd primes.

## Statement echo

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

## Mathematical result

The pairs (0,1) and (1,1) answer the question affirmatively. Write fₙ=Fₙ(0,1)
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

## Literature scope and remaining boundary

The versioned preprint and journal text both explicitly pose Question 5.3.
The accepted assignment's bounded named source screen reports no exact
settlement within its stated readings. Broader web, citation, code and
Reservoir coverage remains unmeasured; no global absence or publication
priority claim follows. This is a Stage A proof candidate, before independent
mirror review, registration completion, freezing and publication.
