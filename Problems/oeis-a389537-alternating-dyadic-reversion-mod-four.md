---
slug: oeis-a389537-alternating-dyadic-reversion-mod-four
bibkey: hanna2025a389537
doi: null
url: https://oeis.org/A389537
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour
---

# Alternating dyadic reversion modulo four for A389537

## Problem

Paul D. Hanna, OEIS A389537, Nov 03 2025, gives the following NAME and
COMMENT. These quotations are copied verbatim from the claim in
`Library/Arith/hanna2025a389537.md`.

NAME:

> G.f. A(x) satisfies A( A(x) - x ) = A(x)^2.

COMMENT:

> Conjecture: for n > 2, a(n) == 2 (mod 4) when n = 3*2^k for k >= 0 otherwise a(n) is divisible by 4.

The formal target uses the normalized integral formal power series with
`A(0) = 0` and `a(1) = 1`.

## Motivation

This is a first-tier recent OEIS conjecture selected by the search seat.
The KPI is open problems resolved. The target is the assertion for every
natural-number index greater than two, not a finite prefix computation.

## Gap

The supplied search report found no proof in its searched scope: the search
seat read the OEIS entry and revision history on 2026-09-09 and searched
arXiv, MathOverflow, and GitHub by identifier. This Stage-B seat had no
network and did not independently repeat those searches. Absence within
that scope does not establish exhaustive literature coverage or priority.

## Route

Construct A as the compositional inverse of the explicit integral series
R = sum_{j >= 0} (-1)^j x^{2^j}. `inverseSeries` represents R through a
private terminating coefficient recursion, with linear coefficient one.
Coefficient cancellation proves `inverse_equation`, R + R(X^2) = X.
The two-sided reversion identities give `generating_equation`, namely
A(0) = 0, a(1) = 1, and A(A - X) = A^2. For any other normalized solution,
its inverse satisfies the same dyadic equation; strong induction on
coefficients proves inverse uniqueness and hence `generating_unique`.

Over ZMod 4, `reduced_perturb` derives R(S + 2T) = R(S) + 2T for
zero-constant S and T: squaring erases the perturbation because 4 = 0.
The dyadic support series D = sum_{j >= 0} x^{3*2^j} satisfies
D = X^3 + D(X^2). Coefficient uniqueness then gives
R(X + X^2) = X + 2D, so reversion yields A = X + X^2 + 2D modulo four.
`hanna_conjecture` reads off residue two at n = 3*2^k and residue zero
elsewhere for every n > 2, proving both biconditionals. The proof has no
D5 import and has generality G.

## Falsifier

A counterexample index n > 2 for the normalized series, with residue other
than two at n = 3*2^k or with nonzero residue modulo four at an index outside
that family, would contradict the assertion. The orchestrator's exact
numerical check is supporting evidence only, not the unbounded proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `inverse_equation`, `generating_equation`, `generating_unique`.
- Axioms: std3, exactly `propext`, `Classical.choice`, `Quot.sound` for
  each public theorem, as reported in the implementation seat's envelope.
- The integer coefficients are constructed by integral reversion; the
  equation and normalized uniqueness are proved, not assumed.

## Triage

`theorem`. The formal proof closes the universal coefficient congruence
assertion recorded by OEIS, with the normalized series identified by the
equation and uniqueness companions.

## ASSUMED-UNVERIFIED

The quotations and attribution were supplied by the orchestrator; this
seat copied the quotations from the Library note. The OEIS revision history
was read by the search seat, not by this seat. Literature scope was the
OEIS entry and history plus identifier searches on arXiv, MathOverflow,
and GitHub on 2026-09-09; this seat had no network. No exhaustive literature
search or first-publication priority is claimed. Source-to-Lean identification,
the search report, and the orchestrator's numerical checks are not
kernel-checked facts. The std3 readout is attributed to the implementation
seat rather than a Stage-B rerun.
