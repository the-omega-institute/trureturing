---
slug: oeis-a380558-parity
bibkey: hanna2025a380558
doi: null
url: https://oeis.org/A380558
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/A380558
---

# Parity of the A380558 square-reversion series

## Problem

OEIS A380558, by Paul D. Hanna (February 13, 2025), defines the generating
series `A(x) = Sum_{n>=2} a(n)*x^n` through
`A(x - A(x)) = x^2/(1 - x^2)`. Its comment states:

> Conjecture: a(n) is odd iff n = 2*A004760(k) for some k > 1, where A004760 lists numbers whose binary expansion does not begin 10.

The formal target constructs an integral series with zero coefficients at
degrees zero and one, proves that source equation and uniqueness among all
similarly normalized integral solutions, and proves for every natural `n`:

`Odd ([x^n]A) <-> n = 2 or there exist m,j in N with n = 2*m and
3*2^j <= m < 4*2^j`.

This is the source conjecture with its natural zero extension at degrees zero
and one. A004760 has offset one: its first values are `0,1,3,6,7,...`.
The condition `k>1` retains `1`, giving `n=2`; all later values lie in the
half-open dyadic intervals displayed above. Neither `m` nor `j` is the OEIS
index `k`.

## Motivation

This was a named, literature-open parity conjecture in a 2025 OEIS entry. The
target is its complete unbounded bidirectional assertion, with the source
series identified uniquely over the integers.

## Gap

The A380558 entry's formula field already supplies
`A = B^2/(1-B^2)` with `B(x-A(x))=x`. The project already proves the integral
reversion series `B`, its uniqueness, and its reduction to a characteristic-two
lacunary series `L` in
`D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity`.
The neighboring invariant module proves `L = X + X^2 + X^2 L^2`.
These are premises, not new claims of this resolution.

The A380558 entry still labels parity a conjecture in revision 12 on
2026-09-28. The project PR search for `A380558` returned no prior PR;
the pre-proof literature and code search, including its stated access
limits, is recorded in preregistration issue #8272. This is a
not-found-in-searched-scope assessment, not a claim of exhaustive priority.
The literature note records the exact OEIS revision fields and retrieval
hashes for both A380558 and A004760.

## Route

The new characteristic-two calculation sets `T=L/(1-L)` and derives
`T=X+X^2+(1+X)T^2`. Frobenius then gives `t_0=0`, `t_1=1`, `t_2=0`, and
`t_n=t_floor(n/2)` for every `n>=3`. Strong induction identifies the ones as
`n=1` or a member of `[3*2^j,4*2^j)`. The integral source series reduces to
`T^2`, excluding all odd degrees and doubling the interval indices.

For source identity, substitution carries the existing reversion equation
from `B` to `A=B^2/(1-B^2)`. For uniqueness, the compositional inverse of
`X-F` converts any normalized source solution `F` back to a series satisfying
the existing unique `B` equation. The inverse-unit denominators have constant
coefficient one throughout.

## Falsifier

An index where the unique normalized source series has the opposite parity
from the stated support would falsify the conjecture. A finite prefix cannot
establish the universal result; a source-normalization or formal-division
error would invalidate the identification with OEIS rather than refute it.

## Evidence

- Lean source: `D5/S1/Recurrence/Parity/A380558.lean`, public theorem `result`.
- Source-bound registration: `Reg/D5/S1/Recurrence/Parity/A380558.lean`;
  the current Lean report records `declared_validated` with a complete
  source-equivalence bridge.
- The theorem and registration each depend only on `propext`,
  `Classical.choice`, and `Quot.sound` in the current report.
- The literature note records the exact OEIS fields, revision markers,
  retrieval hashes, and plain-text locators.

## Triage

`theorem`. The result proves the conjecture for every natural degree of the
unique normalized integral solution.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not certify first-publication
priority. Source-to-Lean identification is reviewed against the OEIS fields,
but is not a kernel theorem. This result does not settle the separate A185897
conjecture or claim novelty for the published reversion transform.

Preregistration: issue #8272.
