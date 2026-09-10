---
slug: oeis-a378581-theta-self-composition-mod-four
bibkey: hanna2025a378581
doi: null
url: https://oeis.org/A378581
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour
---

# The theta self-composition coefficients modulo four

## Problem

OEIS A378581 (Paul D. Hanna, Jan 08 2025), as quoted in
`Library/Recurrence/hanna2025a378581.md`:

NAME:
> G.f. A(x) satisfies: A(x*A(x)) = theta_3(x) = 1 + 2*Sum_{n>=1} x^(n^2).

COMMENT:
> Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is square, else a(n) is divisible by 4 if n is nonsquare.

## Motivation

This is a first-tier OEIS conjecture from a 2025 entry. The KPI is open
problems resolved: the target is the assertion at every positive index.

## Gap

The supplied search report found no proof: the search seat read the OEIS entry
and revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not
independently repeat those searches. A negative search is not a proof of
publication priority.

## Route

`thetaSeries` is 1 + 2·Σ_{j≥1} X^{j²}, defined coefficientwise:
`coeff_thetaSeries` gives 1 at n = 0, 2 at positive squares, and 0 otherwise.
The series A is the stabilised fixed point of the triangular self-composition
equation, constructed by `approximation`. The private lemma `triangular`
isolates the degree-n coefficient of F.subst(X·F), with multiplier one on
coeff n F; `step_agree` then gives contraction. Thus `generating_equation`
states A(0) = 1 and A.subst(X·A) = thetaSeries, exactly the OEIS NAME, and
`generating_unique` covers every B with constant coefficient 1 satisfying it.

Over ZMod 4, `weighted_subst` proves that annihilating an argument difference
annihilates the substituted-series difference. Write the reduced theta series
as Θ̄ = 1 + 2·S̄. Since X·Θ̄ − X = 2X·S̄ and 2·2 = 0, the lemma gives
2·S̄(X·Θ̄) = 2·S̄. Hence Θ̄ solves the same equation (`reduced_solution`),
and uniqueness gives `mod_four_identity`, namely Ā = Θ̄ modulo 4.
Finally `hanna_conjecture` reads off, for n > 0,
`(a n % 4 = 2 ↔ IsSquare n) ∧ (a n % 4 = 0 ↔ ¬ IsSquare n)`
from `coeff_thetaSeries`. The module has no D5 import and has generality G.

## Falsifier

A positive index n whose coefficient is not 2 modulo 4 at a square, or is not
0 modulo 4 at a nonsquare, would falsify the assertion. The orchestrator's
exact coefficient check is supporting evidence only, not the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `coeff_thetaSeries`, `generating_equation`, `generating_unique`,
  `mod_four_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported for
  all five public theorems in the implementation seat's axiom output.

## Triage

`theorem`. The formal proof closes the universal assertion recorded by OEIS.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator and copied from the Library
note. The OEIS entry and revision history were read by the search seat on
2026-09-09, not by this network-disabled Stage-B seat. The reported literature
scope was the OEIS entry and revision history plus identifier searches on
arXiv, MathOverflow, and GitHub; it was not an exhaustive literature review.
First-publication priority and the source-to-Lean identification are not
kernel-checked facts.
