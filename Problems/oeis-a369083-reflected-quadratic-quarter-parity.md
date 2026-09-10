---
slug: oeis-a369083-reflected-quadratic-quarter-parity
bibkey: hanna2024a369083
doi: null
url: https://oeis.org/A369083
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity
---

# Binomial parity of the A369083 coefficients

## Problem

OEIS A369083, Paul D. Hanna, Jan 12 2024, gives the following NAME and
COMMENT, quoted verbatim from `Library/Recurrence/hanna2024a369083.md`:

> Expansion of g.f. A(x) satisfying A(x) = 1 + x*(5*A(x)^2 - A(-x)^2)/4.

> Conjecture: a(n) == binomial(4*n+3,n) (mod 2) for n >= 0 (cf. A263133).

## Motivation

This is a first-tier OEIS conjecture from the 2024 entry. The target is the
assertion for every natural index, including zero. KPI: open problems resolved.

## Gap

The supplied search found no proof: the search seat read the OEIS entry and
revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat those external checks. This search scope does not establish exhaustive
absence of a published proof.

## Route

Construct A over the integers by coefficient stabilisation with exact division.
The odd-index coefficient of a square is even, proved using the Mathlib
Frobenius identity after reduction modulo two. Thus `generating_equation`
states A(0) = 1 and `4*(A-1) = X*(5*A^2-rescale(-1,A)^2)`, the NAME with its
denominator cleared. `generating_unique` covers every integer series B with
constant coefficient one satisfying that equation.

`reflection_linear` combines the equation with its x -> -x image and cancels
four in integer power series, giving `A(-x) = 5*A - 4 - 6*x*A^2`.
Substitution yields `quartic_equation`:
`1 - 4*x + (10*x-1)*A - (5*x+12*x^2)*A^2 + 15*x^2*A^3 - 9*x^3*A^4 = 0`.
Over ZMod 2 this becomes `F*(1+x*F)^3 = 1`, so H := 1+x*F satisfies
`H^4-H^3 = X`.

The reduced series G of the frozen `AbsoluteReciprocalCubeParity` satisfies
the same equation, using its `generating_equation` with absolute value
invisible modulo two. Its `mod_two_identity` identifies G with
`1 + sum_{n>=1} binomial(4*n-1,n)*X^n`. Factoring
`H^4-H^3-G^4+G^3` through a unit gives this module's `mod_two_identity`,
`1 + X*reduction(A) = reduction(integer G)`. Coefficient extraction gives
`a(n) == binomial(4*n+3,n+1) (mod 2)`. The identity `choose_shift`,
`binomial(4*n+3,n+1) = 3*binomial(4*n+3,n)`, then gives
`hanna_conjecture`: `a n % 2 = (Nat.choose (4*n+3) n : Int) % 2` for every n.
Target generality is I because the proof imports the frozen
`AbsoluteReciprocalCubeParity`, itself generality G.

## Falsifier

A natural index n for which the coefficient a(n) has parity different from
`binomial(4*n+3,n)` would contradict the assertion. The orchestrator's exact
coefficient check is supporting evidence only, not a proof for all indices.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/ReflectedQuadraticQuarterParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `reflection_linear`,
  `quartic_equation`, `choose_shift`, `mod_two_identity`.
- `generating_equation` states the NAME multiplied by 4, together with
  `constantCoeff A = 1`, over integer power series. After embedding into
  rational power series, this is equivalent to the NAME's divided equation.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for all seven
  public theorems, as reported by the implementation seat.
- Frozen prerequisite: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity`,
  statement_id `sha256:a7484b050055466f1a3091c41ffc3856281a6de69fd76b14ba71577ef1c07c75`.

## Triage

`theorem`. The formal proof resolves the coefficient assertion at every
natural index for the uniquely constructed integer series.

## ASSUMED-UNVERIFIED

The quotations and attribution were supplied by the orchestrator and copied
from the Library note. The OEIS entry and revision history were read by the
search seat on 2026-09-09, not by this seat. The reported literature scope was
identifier search on arXiv, MathOverflow, and GitHub; this seat had no network.
The searches did not establish exhaustive literature coverage or
first-publication priority. Source-to-Lean identification and the
orchestrator's exact numerical check are not kernel-checked facts.
