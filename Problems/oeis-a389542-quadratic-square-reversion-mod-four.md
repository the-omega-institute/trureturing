---
slug: oeis-a389542-quadratic-square-reversion-mod-four
bibkey: hanna2025a389542
doi: null
url: https://oeis.org/A389542
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour
---

# Quadratic square reversion modulo four for A389542

## Problem

OEIS A389542, Paul D. Hanna, Nov 01 2025, supplies the following NAME
and COMMENT, quoted verbatim from `Library/Recurrence/hanna2025a389542.md`:

> G.f. A(x) satisfies A( A(x)^2 - x^2 ) = 4*A(x)^3.

> Conjecture: for n > 1, a(n) == 2 (mod 4) if n = 2^k + 1 (for some k >= 0) otherwise a(n) is divisible by 4.

## Motivation

This is a first-tier OEIS conjecture from the 2025 entry. The KPI is open
problems resolved: the target proves the coefficient classification for every
index greater than one, together with existence and normalized uniqueness.

## Gap

The supplied search found no proof: the search seat read the OEIS entry and
revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those readings or searches. The gap is a universal proof,
not a finite coefficient check.

## Route

Degree contraction constructs the integral fixed point
`H = -X - H^2 - 2*X*H(4*X^3)`. Set `R := X*(1 + 2*H)` (`inverseSeries`);
`inverse_equation` proves `R^2 = X^2 - R(4*X^3)`. Its compositional inverse
`A` (`generatingSeries`) has integer coefficients. Transporting the identity
through inversion gives `generating_equation`: `A(0) = 0`, `a(1) = 1`, and
`A.subst(A^2 - X^2) = 4*A^3`, exactly the OEIS equation. For every normalized
integer solution, `generating_unique` follows by injectively mapping to the
rationals, proving uniqueness of the inverse equation, and reverting again.

Modulo two, H is the reduction K of the frozen integer Catalan series from
`CatalanCompositionSquareParity`: `K + K^2 = X`, with support `{2^j}`.
The lift of `A*H(A) = X*K` modulo two yields `mod_four_identity`,
`A = X + 2*X*K` modulo four. Thus `hanna_conjecture` reads off, for `n > 1`,
`a(n) = 2` modulo four iff `n = 2^k + 1`; otherwise `4` divides `a(n)`.
The target has generality I because it imports the frozen Catalan module,
which itself has generality G.

## Falsifier

A counterexample index `n > 1` whose coefficient has remainder other than two
at `n = 2^k + 1`, or is not divisible by four at any other index, would falsify
the conjecture. The orchestrator's exact coefficient check is supporting
evidence only; the theorem has no finite index bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `inverse_equation`, `generating_equation`, `generating_unique`,
  and `mod_four_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported for
  each public theorem by the implementation seat.
- Frozen dependency: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`,
  statement_id `sha256:0033f4a50a501546a5f332ce1203c8cf1a936428e7a155a06a0443bb0f0f6232`.

## Triage

`theorem`. The formal statement proves the universal OEIS coefficient
conjecture for the unique normalized integer solution.

## ASSUMED-UNVERIFIED

The quotations and attribution were supplied by the orchestrator. The OEIS
entry and revision history were read by the search seat on 2026-09-09, not by
this seat. The reported literature scope was identifier search on arXiv,
MathOverflow, and GitHub; it does not establish exhaustive literature coverage
or publication priority. This seat had no network access. Source-to-Lean
identification and the orchestrator's exact check are not kernel-checked facts.
