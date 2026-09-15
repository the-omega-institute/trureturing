---
slug: oeis-a245786-integrality-gcd-record-refutation
bibkey: krizek2014a245786
doi: null
url: https://oeis.org/A245786
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation
---

# Refutation of the A245786 integrality-implies-gcd-record conjecture

## Problem

OEIS A245786, NAME (verbatim):

> Numbers n such that k(n) = (n/tau(n) + sigma(n)/n) is an integer.

COMMENT conjecture line (verbatim; Jaroslav Krizek, Aug 15 2014):

> Conjecture: Subsequence of A216793.

OEIS A216793, NAME (verbatim; Michel Marcus, Sep 16 2012):

> Numbers n such that gcd(sigma(n), n) > gcd(sigma(m), m) for all m < n.

The literal claim is
`∀ n ≥ 1, IsMember n → IsRecord n`, where `IsMember` is the A245786
integrality condition and `IsRecord` is the A216793 strict gcd-record
condition.

## Motivation

This first-tier OEIS conjecture was printed in 2014 and remains a universal
subsequence claim linking an integrality condition to record values of
`gcd(sigma(n), n)`. A certified counterexample resolves the literal
conjecture without proposing a corrected statement.

## Gap

Preregistration issue #7517 and its probe report record searches dated
September 13, 2026. OEIS history revisions #1 through #16 only restate the
sequence and conjecture; no proof, refutation, or withdrawal appears there.
Exact searches returned 0 results on arXiv and 0 on MathOverflow. OpenAlex
returned 0 once and was unavailable on the repeat attempt. GitHub was
rate-limited, so that surface is `ASSUMED-UNVERIFIED`. The sibling sequence
A245778 was refuted by Max Alekseyev on July 28, 2026, but that result has a
different premise and does not settle this claim. No resolution was found in
the bounded surfaces that could be checked. This does not assert exhaustive
literature coverage or publication priority.

## Route

Let `N = 275890944 = 2⁸·3·7·19·37·73`. Multiplicativity gives
`tau(N) = 288` and `sigma(N) = 919636480`, hence
`N/288 + 919636480/N = 957958`. Thus `N` is a member of A245786, and
`gcd(sigma(N), N) = 91963648`.

For the smaller number
`M = 142990848 = 2⁹·3²·7·11·13·31`, multiplicativity gives
`sigma(M) = 571963392 = 4M`, so `gcd(sigma(M), M) = M`. Therefore
`M < N` and
`gcd(sigma(M), M) = 142990848 > 91963648 = gcd(sigma(N), N)`.
Consequently `N` is a member but not a record, refuting the subsequence
conjecture.

## Falsifier

A proof that every positive A245786 member satisfies the A216793 strict
record condition would falsify this refutation. The kernel-checked instance
at `N = 275890944` and its smaller witness `M = 142990848` prove the
opposite, so such a proof would contradict the formal result.

## Evidence

- Lean module:
  `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The probe recorded whole-file kernel type-checking in 19.2 seconds.
- The orchestrator independently checked the exact values for `N` and `M`
  with SymPy and found the first six listed members unbeaten by smaller
  multiply-perfect numbers.
- The probe independently found the members at most `2·10⁵` to be exactly
  `{1, 672, 4680, 30240}`, all record points, and checked the factorizations,
  divisor counts, divisor sums, gcd values, and rational value used here.

The bounded searches are supporting evidence only. The formal result uses
the single member `N = 275890944` and the smaller witness `M = 142990848`.

## Triage

`theorem`. The certified member at `N = 275890944` is not a gcd record, so
it refutes the literal subsequence conjecture. It asserts no corrected
statement and no claim about any other input.

## ASSUMED-UNVERIFIED

The repeat OpenAlex search was unavailable, and the GitHub search was
rate-limited, so those surfaces were not fully verified. The literature
search is bounded and does not establish exhaustive coverage or publication
priority. The counterexample `N = 275890944` is not claimed to be the least
counterexample.
