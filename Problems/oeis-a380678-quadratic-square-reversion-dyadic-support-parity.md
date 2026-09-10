---
slug: oeis-a380678-quadratic-square-reversion-dyadic-support-parity
bibkey: hanna2025a380678
doi: null
url: https://oeis.org/A380678
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity
---

# Dyadic support of the odd coefficients of A380678

## Problem

Paul D. Hanna, OEIS A380678, February 2025. The Library note records the
month and year but not the exact `%A` line date. The following NAME and
COMMENT are copied verbatim from `Library/Recurrence/hanna2025a380678.md`.

NAME:

> G.f. A(x) satisfies A( x - A(x)^2/(1 - A(x)^2) ) = x.

COMMENT:

> Conjecture: for n>= 1, a(n) is odd iff n is a term of A027383, where A027383(2*m) = 3*2^m - 2 and A027383(2*m+1) = 4*2^m - 2.

## Motivation

This is a first-tier OEIS conjecture from the 2025 entry. KPI = open problems
resolved. The target is a parity classification for every index n >= 1.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching by identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did
not independently repeat those searches. This is a bounded search report,
not a claim of exhaustive literature coverage or publication priority.

## Route

Construct A over the integers as the stabilised fixed point of the
reversion-type contraction `f + X - f.subst (X - f^2 * invOfUnit (1-f^2) 1)`.
The square-denominator argument gains one degree of coefficient agreement:
its difference factors as `(f-g)*(f+g)` times the two unit inverses. The
inner argument has linear coefficient one, so substitution has multiplier
1 on a(n) at the first differing coefficient. Thus `generating_equation`
states A(0) = 0, a(1) = 1, and exactly the NAME equation, represented by
`A.subst (X - A^2 * invOfUnit (1 - A^2) 1) = X`.
`generating_unique` covers every normalised integral solution.

Over ZMod 2, write Abar for the coefficientwise reduction of A. Characteristic
two gives `1 - Abar^2 = (1 - Abar)^2`. The reduced equation is therefore
exactly the equation that the frozen
`QuadraticReversionDyadicSupportParity.lacunary_reversion` proves for
`lacunarySeries`. Reduced uniqueness gives `mod_two_identity`, namely
`Abar = lacunarySeries`. Its coefficient formula gives `hanna_conjecture`:
for n >= 1, `Odd (a n)` iff there exists a natural m with
`n + 2 = 3 * 2^m` or `n + 2 = 4 * 2^m`.
These are precisely the COMMENT's A027383 support families:
`A027383(2*m) = 3*2^m - 2` and `A027383(2*m+1) = 4*2^m - 2`.

Target generality is I because the module imports the frozen
`D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity`, itself
generality G. Its statement_id is
`sha256:64c91825be7bdc54e67d6c12e38a5e78833d3aa76de1009a7dfea7dd81ebe781`.

## Falsifier

A counterexample index n >= 1 where the coefficient of the normalised NAME
solution is odd without belonging to either family, or even while belonging
to either family, would falsify the assertion. The orchestrator's exact
numerical check is supporting evidence only; no finite prefix replaces the
universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for each public
  theorem, as reported by the implementation seat's single-file Lean check.

## Triage

`theorem`. The formal proof establishes the universal parity assertion for
the constructed series and proves its NAME equation and normalised uniqueness.

## ASSUMED-UNVERIFIED

The OEIS quotes were supplied by the orchestrator and copied from the Library
note. February 2025 is the supplied entry date at month precision; the exact
`%A` line date was absent from that note and was not independently verified.
The OEIS revision history was read by the search seat, not by this seat.
The reported literature scope was the OEIS entry and revision history plus
identifier searches on arXiv, MathOverflow, and GitHub on 2026-09-09; it was
not exhaustive. Source-to-Lean identification, first-publication priority,
and the orchestrator's numerical receipt are not kernel-checked facts.
