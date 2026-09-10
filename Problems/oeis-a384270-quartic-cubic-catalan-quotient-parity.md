---
slug: oeis-a384270-quartic-cubic-catalan-quotient-parity
bibkey: hanna2025a384270
doi: null
url: https://oeis.org/A384270
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity
---

# Parity of the A384270 coefficients

## Problem

OEIS A384270, Paul D. Hanna, Jul 10 2025. The following NAME and COMMENT
are copied verbatim from the claim in `Library/Arith/hanna2025a384270.md`.

NAME:

> G.f. satisfies A(x) = A(x^4 + 4*x*A(x)^4) / A(x^3 + 3*x*A(x)^3).

COMMENT:

> Conjecture: a(n) is odd iff n = 2^k for k >= 0.

**范围与诚实边界**: The module formalizes the cross-multiplied identity
`A·A(x³+3xA³) = A(x⁴+4xA⁴)`, with `A(0)=0` and `a(1)=1`. The displayed
denominator has zero constant term, so it is not a unit in the integer
formal power-series ring. The public parity theorem covers every positive
natural index; the constant coefficient is zero by `generating_equation`.

## Motivation

This is a first-tier recent OEIS conjecture, selected as a 2025 small
conjecture. KPI = open problems resolved. The target is the unbounded parity
assertion, supported by construction and uniqueness of the normalized series.

## Gap

The supplied search report found no proof in its searched scope: the search
seat read the OEIS entry and revision history on 2026-09-08 and searched by
identifier on arXiv, MathOverflow, and GitHub. This Stage-B seat had no network
access and did not repeat those searches. This is a scoped negative search
result, not an exhaustive literature or first-publication claim.

## Route

Write `A = X·B`, with `B(0)=1`, and cancel `X⁴`. An integral contracting
update uses only addition, subtraction, multiplication, and substitution,
without division. Its approximations stabilize coefficientwise; the diagonal
limit constructs the integer solution and proves `generating_equation`.
The private `step_agree` improves agreement below degree d to agreement below
degree d+1 over arbitrary commutative rings. Induction gives uniqueness,
specialized to integer series in the public `generating_unique`.

Over `ZMod 2`, the binary Catalan series C is built using Mathlib's
`substInvOfIsUnit` for `X+X²`. Its identity `C+C²=X` gives
`X³+XC³=C³+C⁶` (`binary_cubic_inner`), and substitution into the left inverse
identity gives `C(C³+C⁶)=C³` (`binary_cubic_reversion`). Together with
Frobenius `C(X⁴)=C⁴`, these establish the reduced functional equation.
Uniqueness identifies the reduction of A with C. Strong induction on the
coefficient support then proves `hanna_conjecture`: exactly the powers of two
have odd coefficients. No D5 module is imported; generality is G.

## Falsifier

A positive index n for which `Odd (a n)` differs from `∃ k, n = 2^k` would
contradict the assertion. The orchestrator's exact coefficient check is
supporting evidence only and does not replace the unbounded theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/QuarticCubicCatalanQuotientParity.lean`.
- Main public theorem: `hanna_conjecture`.
- Companion public theorems: `generating_equation`, `generating_unique`.
- Axioms: std3, exactly `propext`, `Classical.choice`, `Quot.sound` for each
  public theorem, as reported by the implementation seat's `print axioms`.
- The exact computation supplied by the orchestrator is supporting evidence;
  the parity theorem is quantified over every positive natural index.

## Triage

`theorem`. The formal proof closes the normalized series' parity assertion
recorded by OEIS, with its defining equation interpreted as stated above.

## ASSUMED-UNVERIFIED

The OEIS quotations, attribution, and date were supplied by the orchestrator
and recorded in the Library note. The OEIS revision history was read by the
search seat on 2026-09-08, not by this Stage-B seat. The literature search
covered the OEIS entry and revisions plus identifier searches on arXiv,
MathOverflow, and GitHub; this seat had no network access. First-publication
priority, exhaustive literature coverage, and source-to-Lean identification
are not kernel-checked facts. The reported axiom closure and orchestrator's
exact check were not independently rerun by this seat.
