---
slug: oeis-a393867-prime-power-shift-log-derivative
bibkey: hanna2026a393867
doi: null
url: https://oeis.org/A393867
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative
---

# Prime divisibility of the A393867 logarithmic-derivative terms

## Problem

Paul D. Hanna's OEIS entries A393866 and A393867, Mar 29 2026, specify:

A393866 NAME (quoted verbatim in `Library/Recurrence/hanna2026a393867.md`):

> G.f. A(x) satisfies [x^n] A(x)^prime(n) = prime(n) * [x^(n-1)] A(x)^prime(n) for n >= 1.

A393867 NAME (quoted verbatim in the same note):

> Logarithmic derivative of A393866.

With constant coefficient 1 for A, this means
`a(n) = [x^(n-1)] A'(x)/A(x)`, with offset 1. This dossier concerns A393867.
Its target COMMENT (quoted verbatim in the same note) is:

> Conjecture: a(n) is divisible by prime(n) for n > 1.

The second A393867 comment, "Conjecture: all terms are odd.", is not resolved.
A393866 FORMULA (2), "[x^n] A'(x)/A(x) == 0 (mod prime(n)) for n > 1
(conjecture - see A393867)", is refuted as printed by the companion theorem;
it is not a second resolution claim in this dossier.

## Motivation

This is a first-tier OEIS conjecture from the 2026 entry. The KPI is open
problems resolved: one claim for A393867's divisibility conjecture.

## Gap

No proof was found in the supplied search: the search seat read the OEIS entry
and revision history on 2026-09-09 and searched the identifiers on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat those searches. Absence from this search is not a proof of priority.

## Route

`prime n = Nat.nth Nat.Prime (n - 1)` is one-based, so `prime 1 = 2`;
`lt_prime` proves `n < prime n` for `1 <= n`. The series F is constructed by
exact integer corrections, degree by degree. Expanding `(P + c*X^n)^p`
separates the endpoint terms; every interior binomial coefficient is divisible
by the prime. In the Lean implementation, expansion of `(1 + (B - 1))^p`
establishes low-degree divisibility, while difference-of-powers factorization
establishes the linear change of the corrected coefficient.

`generating_equation` states F(0) = 1 and, for every n >= 1,
`[x^n] F^(prime n) = prime n * [x^(n-1)] F^(prime n)`, exactly the A393866 NAME
quoted above. `generating_unique` covers every integer series B with constant
coefficient 1 satisfying that same family. `prime_dvd_coeff_pow` gives
`prime n | [x^j] F^(prime n)` for `1 <= j < prime n`.

`logDerivative` is F' times the unit inverse of F, using Mathlib's
`PowerSeries.derivative` and `invOfUnit`. `a393867 n` is its coefficient of
degree n-1, matching "Logarithmic derivative of A393866." with offset 1.
`log_derivative_identity` states `X*(F^n)' = n*(X*logDerivative)*F^n`.
Extracting degree n with exponent `prime n`, cancelling the nonzero prime,
and removing the convolution's constant-factor term gives `hanna_conjecture`:
for n > 1, `prime n | a393867 n`. The proof uses the equivalent unshifted
private derivative identity at degree n-1.

The companion `printed_formula_false` refutes A393866's printed formula (2)
as written: its degree n is an index-shifted misprint of A393867's conjecture.
At n = 2, `[x^2] F'/F = 25`, which is not divisible by `prime 2 = 3`.
This companion is discussed only in prose as source clarification. There is
exactly one resolution claim, `ResolutionKind.Proved` on `hanna_conjecture`,
for the A393867 conjecture. The module has Mathlib-only imports, no D5 import,
and generality G.

## Falsifier

A counterexample index n > 1 for which `prime n` does not divide the degree
n-1 coefficient of F'/F would falsify the target. The orchestrator's exact
numerical check is supporting evidence only; it does not replace the universal
theorem or resolve the separate oddness conjecture.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `lt_prime`, `generating_equation`, `generating_unique`,
  `prime_dvd_coeff_pow`, `log_derivative_identity`, `printed_formula_false`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported for
  all seven public theorems by the implementation seat's `#print axioms` checks.

## Triage

`theorem`. The single resolution claim proves the A393867 divisibility
conjecture for all n > 1.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator; the two NAME lines and
target COMMENT were copied from `Library/Recurrence/hanna2026a393867.md`.
The search seat, not this seat, read the OEIS entry and revision history on
2026-09-09. The supplied literature search covered identifier searches on
arXiv, MathOverflow, and GitHub. This seat had no network access. Exhaustive
literature coverage, first-publication priority, and the source-to-Lean
identification are not kernel-checked facts. The oddness comment and the full
parenthetical in A393866 formula (2) came from the orchestrator's brief.
