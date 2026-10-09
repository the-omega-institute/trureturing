---
slug: kimberling-array-first-occurrence-l4v5
bibkey: ashburn2026kimberling
doi: 10.48550/arXiv.2610.05776
url: https://arxiv.org/abs/2610.05776v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/KimberlingArrayFirstOccurrence.result
---

# First occurrences in Kimberling's array

## Problem

Alex Ashburn, arXiv:2610.05776v1, Section 5, Conjecture 15:

> For every v ≥ 2, the least N with a(N) = v is L_{4v−5}.

Put φ = (1 + √5)/2 and R_i = {⌊kφ^i⌋ : k ≥ 1}, for positive natural
row indices i. The occurrence count a(N) is the number of rows containing
N. The Lucas sequence has L₀ = 2, L₁ = 1 and L_{n+2} = L_{n+1} + L_n.

The Lean `claim` says, for every natural v ≥ 2, both a(L_{4v−5}) = v and
that every positive N < L_{4v−5} has a(N) ≠ v. The count uses the finite
index interval 1 ≤ i ≤ N; the proved row-index bound shows that this loses
no containing row.

## Motivation

The source proves that each positive occurrence count is attained infinitely
many times. First occurrences identify the smallest representatives of
these classes and relate their growth to odd-indexed Lucas numbers.

## Gap

Proposition 10 establishes attainment at L_{4v−5}; Conjecture 15 asks for
universal minimality. The gap is a bound on the smallest common value of
two arbitrary positive rows, followed by a finite count argument. The
source supplied with the task is v1; no claim of exhaustive literature
priority is made.

## Route

Consecutive rows are disjoint: the Fibonacci inverse-power identity makes
an integer weighted average lie strictly between N and N+1 if the same
N belongs to both rows.

For 1 ≤ i < j, suppose N belongs to both rows and N < L_{2i+1}. Choose
positive multipliers k,l and put d = j−i ≥ 2 and u = k−lφ^d. The floor
bounds give k < φ^{i+1}, lφ^d < φ^{i+1} and 0 < |u| < φ^{−i}.
Its conjugate satisfies |u′| < φ^{i+1}(1+φ^{−2d}), so its nonzero integral
norm has absolute value less than φ(1+φ^{−4}) < 2. Hence the norm is ±1.

The unit classification in ℤ[φ] and the negative golden coefficient imply
u = ψ^r = (−1)^r φ^{−r}, with ψ = −φ^{−1} and r ≥ i+1. Coefficient
comparison gives lF_d = F_r and d ≤ r. If r ≥ i+2, the conjugate equation
k = φ^r+lψ^d contradicts k < φ^{i+1}. Thus r = i+1. For even d, the
same equations give lφ^j ≥ φ^{2i+1} > L_{2i+1}. For odd d, let
H = lL_j and ε = lφ^{−j}, where 0 < ε < φ^{−1}. Then

$$
l\varphi^j=H-(-1)^r\varepsilon,\qquad
k\varphi^i=H+(-1)^r(\varphi^{-1}-\varepsilon).
$$

These multiples straddle the integer H, contradicting their common floor.
Therefore every common value satisfies L_{2i+1} ≤ N.

List any v containing rows in increasing order. Their gaps are at least
two, so the penultimate index is at least 2v−3. Applying the pair bound
and Lucas monotonicity gives the stronger conclusion

$$
v\ge2\ \land\ a(N)\ge v\quad\Longrightarrow\quad L_{4v-5}\le N.
$$

At m = 4v−5, the rows 1,3,…,2v−3 and m contain L_m. The lower odd-row
multiplier is L_{m−i}, and the own-row multiplier is one. These are v
distinct rows. An additional row would force L_{4v−1} ≤ L_{4v−5},
contradicting strict Lucas increase. This proves attainment and minimality.

## Falsifier

A counterexample would be a positive N below L_{4v−5} with exactly v
occurrences, or a target Lucas number with a different occurrence count.
The stronger lower bound excludes the former, and the explicit v-row
construction plus the next threshold excludes the latter. The proof must
retain strict floor bounds, both interval-gap parities, the integer norm
condition, and complete coverage of the finite occurrence count.

## Evidence

`D5/S1/Recurrence/KimberlingArrayFirstOccurrence.result` has the exact
closed type `claim`. The companion module proves the golden unit
classification. Both modules compile with the pinned Lean toolchain.
The settling theorem's axiom closure is `propext`, `Classical.choice`,
`Quot.sound`; there is no `sorry`, new axiom or `native_decide`.

Two independent exact-integer checks through N = 1,000,000 reproduce the
first occurrences 4, 29, 199, 1364, 9349, 64079, 439204 for v = 2,…,8.
The forward enumeration visits 28 rows and 1,618,022 entries. The inverse
membership checker verifies 720,519 containing-row pairs with no violation
of the pair lower bound. These finite computations support the definitions;
the universal conclusion follows from the Lean proof.

Literature: [arXiv:2610.05776v1](https://arxiv.org/abs/2610.05776v1),
Proposition 10 and Conjecture 15; sequence records
[OEIS A128440](https://oeis.org/A128440) and
[OEIS A358359](https://oeis.org/A358359). The proposition's exact row set
for odd m ≥ 3 is {i odd : 1 ≤ i ≤ (m−1)/2} ∪ {m}. The formal attainment
argument uses its explicit positive memberships and the stronger lower
bound to exclude any further rows.

## Triage

`theorem`: Conjecture 15 holds for every v ≥ 2. The stronger implication
from a(N) ≥ v to L_{4v−5} ≤ N is also proved.

`computed`: the two exact-integer enumerations agree on all first
occurrences available through N = 1,000,000.

`open`: no even-indexed Lucas membership classification is proved here.
The source's Proposition 14 proves existence and positivity of the
densities d_v; exact density values or additional bounds are not settled
by this first-occurrence theorem.

### What the settlement shows

- [proved: D5/S1/Recurrence/KimberlingArrayFirstOccurrence.pair_lower_bound]
  The norm-one constraint on an overlapping pair forces an odd Lucas
  threshold. The parity cases exclude every smaller common value.
- [proved: D5/S1/Recurrence/KimberlingArrayFirstOccurrence.occurrence_lower_bound]
  The bound applies to at least v occurrences and does not require a
  positive N hypothesis. Separation of consecutive rows is what turns a
  pair estimate into a threshold for arbitrarily many occurrences.
- [proved: D5/S1/Recurrence/KimberlingArrayFirstOccurrence.lucas_attainment]
  The threshold is sharp for each v ≥ 2. The explicit odd-row witnesses
  attain it, and the next threshold excludes any extra row.
- [proved: D5/S1/Recurrence/KimberlingArrayFirstOccurrence.result]
  The representative used in the source's Theorem 13 is optimal as the
  first occurrence. Its infinite-recurrence argument and Proposition 14's
  density argument remain separate results of the source.
- [computed: `python3 /Users/macstudio/omega-op/s3688/t6-work/lucas_scan.py`
  and `python3 /Users/macstudio/omega-op/s3688/t6-work/carmichael/check_inverse.py`]
  The controls through one million agree with the universal threshold.
- [open] Exact densities and an even-indexed Lucas membership description
  require separate proofs; this settlement addresses the odd-indexed
  first-occurrence family.

## ASSUMED-UNVERIFIED

The supplied v1 source and task brief establish the target's wording;
remote issue metadata, subsequent literature and exhaustive priority have
not been checked in this offline task. The OEIS pages are cited as supplied
sequence references and were not fetched. Scoped Lean and Scribe checks
are separate from repository freezing, complete admission and official
acceptance, which are not performed by this delivery.
