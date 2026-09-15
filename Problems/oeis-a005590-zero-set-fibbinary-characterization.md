---
slug: oeis-a005590-zero-set-fibbinary-characterization
bibkey: sloane2003a005590
doi: null
url: https://oeis.org/A005590
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/StephanA005590ZeroSetCharacterization
---

# The A005590 zero set at multiples of three is characterized

## Problem

OEIS A005590, NAME (`%N`, verbatim):

> a(0) = 0, a(1) = 1, a(2n) = a(n), a(2n+1) = a(n+1) - a(n).

Ralf Stephan's FORMULA conjecture (`%F`, verbatim):

> Conjecture: a(3n)=0 iff n in A003714. - _Ralf Stephan_, May 02 2003

OEIS A003714, NAME (`%N`, verbatim):

> Fibbinary numbers: if n = F(i1) + F(i2) + ... + F(ik) is the Zeckendorf representation of n (i.e., write n in Fibonacci number system) then a(n) = 2^(i1 - 2) + 2^(i2 - 2) + ... + 2^(ik - 2). Also numbers whose binary representation contains no two adjacent 1's.

The literal proved statement is `∀ n, r(3n)=0 ↔ No11 n`, rendered in Lean as
`∀ n : ℕ, r (3 * n) = 0 ↔ No11 n`, where `r : ℕ → ℤ` satisfies `r(0)=0`,
`r(1)=1`, `r(2n)=r(n)`, and `r(2n+1)=r(n+1)-r(n)`, and where
`No11(n) := ∀ j : ℕ, (n >>> j) % 4 ≠ 3`. The growth rate attributed to
Reznick and the partial recurrences recorded by Chai Wah Wu are NOT claimed.

## Motivation

The OEIS entry has recorded Stephan's zero-set equivalence as a conjecture
since 2003. Identifying its zeros with A003714 connects the signed recurrence
to the standard binary language with no adjacent one bits.

## Gap

The checked A005590 entry still labels the zero-set equivalence "Conjecture",
and the checked revision history contains no settlement. Reznick's 1985 paper
addresses continued-fraction extremal behavior, Allouche and Shallit develop
the general theory of regular sequences, and Chai Wah Wu's 2016 contribution
records partial recurrences; none of those checked sources gives this complete
zero-set classification. Exact searches of arXiv and MathOverflow returned no
matching result. OpenAlex's exact combined phrase search, Crossref's exact
identifier search, and GitHub's exact conjecture-phrase search also returned
zero matches on 2026-09-14. These checked surfaces do not support a publication
priority claim.

## Route

1. Strong induction proves the adjacent-pair invariant
   `I(x,y) = x(x-y)`: `(r(n),r(n+1)) ≠ (0,0)` and
   `0 ≤ r(n) * (r(n)-r(n+1))`.
2. For `Z(n) := (r(3n)=0)`, the defining equations and invariant give
   `Z(2m) ↔ Z(m)`, `Z(4m+1) ↔ Z(m)`, and `¬Z(4m+3)`.
3. The low two bits give the same add-a-bit recurrences for `No11`.
4. Strong induction on `n` combines the even, `4m+1`, and `4m+3` cases.

## Falsifier

A natural number `n` for which exactly one of `r(3n)=0` and `No11(n)` holds
would contradict the theorem. The kernel-checked result quantifies over every
natural number.

## Evidence

- Lean module:
  `D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 3.82 seconds, type checking
  190 milliseconds, and maximum resident set size 1,501,675,520 bytes.
- The orchestrator independently found zero mismatches between `r(3n)=0`
  and `No11(n)` on `[0,20000]`, and checked the adjacent-pair invariant on
  `[0,5000]`.
- The bounded checks support fault detection only; the Lean induction carries
  the universal proof.

## Triage

`theorem`. Stephan's stated equivalence is proved for every natural number
under the literal A005590 recurrence and the binary no-adjacent-ones predicate.

## ASSUMED-UNVERIFIED

The bounded scans do not establish the universal statement. Historical
openness outside the checked OEIS history, arXiv, MathOverflow, OpenAlex,
Crossref, GitHub, and cited-source surfaces is unverified; no exhaustive
literature or priority claim is made.
