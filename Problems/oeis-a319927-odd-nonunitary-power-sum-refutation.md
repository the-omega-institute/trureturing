---
slug: oeis-a319927-odd-nonunitary-power-sum-refutation
bibkey: ianakiev2018a319927
doi: null
url: https://oeis.org/A319927
triage: theorem
motivation_gids:
  - D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation
---

# Refutation of the A319927 odd non-unitary power-sum conjecture

## Problem

OEIS A319927, NAME (verbatim):

> Numbers k such that the sum of the squares of the odd non-unitary divisors of k divides the sum of the squares of the non-unitary divisors of k.

COMMENT conjecture line (verbatim; Ivan N. Ianakiev, Oct 02 2018):

> Conjecture: For any nonnegative integer power p the sum of the p-th powers of the odd non-unitary divisors of a(n) divides the sum of the p-th powers of the non-unitary divisors of a(n).

Peter Munn's COMMENT (verbatim):

> The start of this sequence, including the 58 terms currently shown in the data section, is consistent with a definition "nonsquarefree numbers not divisible by 4", but some larger terms are divisible by 4: for example, a(1305) = 9216 = 2^10 * 3^2. - _Peter Munn_, Sep 21 2020

The PARI membership test (verbatim) is:

> `isok(n) = my(suo = suo2(n)); if (suo, (su2(n) % suo) == 0);`

The AUTHOR line is:

> _Ivan N. Ianakiev_, Oct 02 2018

The first terms printed in the DATA section are `9, 18, 25, 27, 45, 49, 50,
54, 63, 75, ...`.

For natural numbers, define
`nonunitaryDivisors(n) = Nat.divisors(n).filter(d => 1 < gcd(d,n/d))`,
where `n/d` is natural-number division and is exact for every divisor in
`Nat.divisors(n)`. Define `S(k,n)` as the sum of `d^k` over those divisors,
and `O(k,n)` as the corresponding sum after the further filter
`d % 2 = 1`. The source program's nonzero guard is retained in
`member(n) := 0 < n and 0 < O(2,n) and O(2,n) divides S(2,n)`.
The literal refuted statement is
`∀ n : ℕ, member n → ∀ k : ℕ, O k n ∣ S k n`.

The result does not assert the 2022 remark that `p*a(n)` is a term, and it
does not assert anything about A034444 or A048105.

## Motivation

Ianakiev's 2018 comment states a universal divisibility conjecture for every
nonnegative power at every sequence member. One explicit sequence member and
power at which divisibility fails resolves that literal statement.

## Gap

Preregistration issue #7646 and its probe report record searches dated
September 14, 2026. OEIS revisions #1 through #30 leave the conjecture
unchanged; revision #30, dated 2025-02-16, changes only a MathWorld link from
HTTP to HTTPS. The discussion for revision #21 contains Peter Munn's
2020-09-22 question, "Is a(1305) also a counterexample to the conjecture? ...
a(1305) with p = 3, to be more specific." The entry never answered that
question.

Exact searches returned 0 results on arXiv, 0 on MathOverflow, and 0 on
Crossref. OpenAlex autocomplete returned 0 and `/works` returned HTTP 429
(`ASSUMED-UNVERIFIED`). GitHub returned two OEIS program mirrors and issue
#7646 only. Google Scholar returned a CAPTCHA (`ASSUMED-UNVERIFIED`). No
publication-priority or exhaustive-literature claim follows from these
bounded surfaces.

## Route

Finite evaluation gives `O(2,9216)=9` and `S(2,9216)=41243877`, so 9216
satisfies the guarded sequence-membership predicate. At `k=1`, the same
evaluation gives `O(1,9216)=3` and `S(1,9216)=16361`; the latter leaves
remainder 2 modulo 3. Instantiating the universal claim at `n=9216` and
`k=1` therefore yields a contradiction.

## Falsifier

A derivation of the literal universal `claim` would falsify this refutation.
The result supplies `member(9216)` and the incompatible fact that
`O(1,9216)` does not divide `S(1,9216)`.

## Evidence

- Lean module:
  `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.lean`.
- Main theorem: `result : Not claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The profiled Lean process took 4.86 seconds wall time and 641 milliseconds
  of cumulative type checking, with maximum resident set size
  1,781,022,720 bytes. The two `decide` certificates accounted for the
  observed 674 milliseconds of tactic execution.
- The result uses finite evaluation to establish both `member(9216)` and the
  failed divisibility at `k=1`; no private helper declaration is present.

The orchestrator computed
`9216 = 2^10*3^2`, 33 divisors, 29 non-unitary divisors, unitary divisors
`{1,9,1024,9216}`, and the single odd non-unitary divisor `{3}`. Its power-sum
readings are `S(0)=29`, `O(0)=1`; `S(1)=16361=3*5453+2`, `O(1)=3`;
`S(2)=41243877=9*4582653`, `O(2)=9`;
`S(3)=145108537091`, `O(3)=27`, with remainder 17; and remainder 63 at
`k=4`.

For `n <= 10^5`, the orchestrator found 14,211 members and five failures at
`k=1`: `9216, 27648, 46080, 51200, 64512`; every listed value also failed at
`k=3` and `k=4`. The probe independently reproduced these `n <= 10^5`
readings. The search seat reported a C++ scan through `n <= 10^6` with
142,128 members, 54 failures at `k=1`, and least failure 9216.

These bounded computations support the single instance used by `result`.
They do not assert a classification of all failures. Munn's 2020 question
about `p=3` and the 2022 remark are not claimed, and neither are statements
about A034444 or A048105.

## Triage

`theorem`. The sequence member 9216 at `k=1` refutes the literal universal
conjecture. No publication-priority claim is made.

## ASSUMED-UNVERIFIED

OpenAlex `/works`, Google Scholar, the search seat's scan through `10^6`, and
all bounded searches beyond the single finite instance used by `result` are
`ASSUMED-UNVERIFIED`. The literature search is bounded and does not establish
exhaustive coverage or publication priority.
