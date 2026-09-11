---
slug: oeis-a393857-scaled-reversion-mod-six
bibkey: hanna2026a393857
doi: null
url: https://oeis.org/A393857
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/ScaledReversionCongruence
---

# Coefficients of A393857 are one modulo six

## Problem

OEIS A393857, Paul D. Hanna, Mar 11 2026. The following NAME and COMMENT
are quoted verbatim from the claim in `Library/Arith/hanna2026a393857.md`.

NAME:

> G.f. A(x) satisfies A( x - x*A(5*x)/5 ) = x.

COMMENT:

> Conjecture: a(n) == 1 (mod 6) for n >= 1.

## Motivation

This is a first-tier recent OEIS conjecture. KPI = open problems resolved:
the target is the assertion for every positive index. One parametric proof
addresses this entry and the mod-five conjecture in A393856.

## Gap

The supplied search report found no proof in its searched scope: the search
seat read the OEIS entry and revision history on 2026-09-08 and searched by
identifier on arXiv, MathOverflow, and GitHub. This Stage-B seat had no network
access and did not independently repeat those readings or searches.

## Route

Work parametrically in a natural number q. Define the inner series integrally
as `x - x * sum_{n >= 1} q^(n-1) * a(q,n) * x^n`; no division is performed in
the integers. The first-difference lemma `subst_first_difference` isolates
the diagonal coefficient in substitution, and `step_agree` proves that the
correction `f + x - f(inner(f))` gains one degree of agreement. Stabilizing
the approximations constructs the integral solution of `A(inner) = x`.
`generating_equation` proves existence and the cleared rescaling identity;
`generating_unique` proves uniqueness. For positive q,
`generating_equation_rational` states the exact divided OEIS form after mapping
to rational coefficients: `A(x - x*A(q*x)/q) = x`.

Modulo q+1, q becomes -1 and the inner expression becomes `x + x*A(-x)`.
For `E = x/(1-x)` this is `x + x*E(-x) = x/(1+x)`.
`geometric_equation` proves `E(x/(1+x)) = x` over any commutative ring, including
the composite-modulus ring `ZMod 6`, using unit denominators. The same
uniqueness argument forces the reduction of A to equal E, so every
positive-index coefficient is congruent to one (`coeff_congruence`). Setting
q=5 gives `hanna_a393857`; q=4 gives the companion `hanna_a393856`. The module
imports only Mathlib, has no D5 import or frozen D5 prerequisite, and has
generality G.

### 范围与诚实边界

Integral existence and uniqueness hold for every natural q; the divided
rational equation and congruence require q >= 1. The congruence concerns
n >= 1, not the zero constant coefficient. No field or prime-modulus
assumption is used. The separate A393856 parity comment "a(n) is odd iff n
is a power of 2" is not resolved here. Identifying the quoted OEIS sequence
with the formal integral solution is a source-fidelity judgment, not a
kernel-checked fact about the external website.

## Falsifier

An index n >= 1 of the uniquely specified integral sequence with
`a(5,n) % 6 != 1` would contradict the assertion. The orchestrator's exact
check is supporting evidence only; a finite check cannot replace this
unbounded theorem, and this seat did not repeat that computation.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.lean`.
- Main public theorem: `hanna_a393857`.
- General theorem: `coeff_congruence`.
- Companions: `generating_equation`, `generating_unique`,
  `generating_equation_rational`, and `hanna_a393856`.
- Public definitions: `a`, `generatingSeries`, and `inner`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), reported for
  each of the six public theorems in the implementation seat's verification
  receipt. Stage-B did not rerun the axiom inspection.

## Triage

`theorem`. The formal proof closes the mod-six assertion for every positive
index, as a specialization of the general congruence.

## ASSUMED-UNVERIFIED

The quotations, attribution, and date were supplied by the orchestrator and
recorded in the Library note. The OEIS revision history was read by the search
seat on 2026-09-08, not by this seat. The no-proof-found report is limited to
the OEIS entry/history and identifier searches on arXiv, MathOverflow, and
GitHub; it is not an exhaustive literature search or a first-publication
priority claim. Stage-B had no network access. Source-to-Lean identification,
external search results, and the orchestrator's exact check were not
independently verified by this seat.
