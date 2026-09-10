---
slug: oeis-a393856-scaled-reversion-mod-five
bibkey: hanna2026a393856
doi: null
url: https://oeis.org/A393856
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/ScaledReversionCongruence
---

# Coefficients of A393856 are one modulo five

## Problem

OEIS A393856, Paul D. Hanna, Mar 11 2026. The following NAME and COMMENT
are quoted verbatim from the claim in `Library/Arith/hanna2026a393856.md`.

NAME:

> G.f. A(x) satisfies: A( x - x*A(4*x)/4 ) = x.

COMMENT:

> Conjecture: a(n) == 1 (mod 5) for n >= 1.

## Motivation

This is a first-tier recent OEIS conjecture. KPI = open problems resolved:
the target is the assertion for every positive index, not a finite prefix.

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
`geometric_equation` proves `E(x/(1+x)) = x` over any commutative ring, using
unit denominators. The same uniqueness argument over `ZMod(q+1)` forces the
reduction of A to equal E, so every positive-index coefficient is congruent
to one (`coeff_congruence`). The cases q=4 and q=5 give `hanna_a393856` and
`hanna_a393857`, respectively. The module imports only Mathlib, has no D5
import or frozen D5 prerequisite, and has generality G.

### 范围与诚实边界

Integral existence and uniqueness hold for every natural q; the divided
rational equation and congruence require q >= 1. The congruence concerns
n >= 1, not the zero constant coefficient. The separate A393856 comment
"a(n) is odd iff n is a power of 2" is not resolved here. Identifying the
quoted OEIS sequence with the formal integral solution is a source-fidelity
judgment, not a kernel-checked fact about the external website.

## Falsifier

An index n >= 1 of the uniquely specified integral sequence with
`a(4,n) % 5 != 1` would contradict the assertion. The orchestrator's exact
check is supporting evidence only; a finite check cannot replace this
unbounded theorem, and this seat did not repeat that computation.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/ScaledReversionCongruence.lean`.
- Main public theorem: `hanna_a393856`.
- General theorem: `coeff_congruence`.
- Companions: `generating_equation`, `generating_unique`,
  `generating_equation_rational`, and `hanna_a393857`.
- Public definitions: `a`, `generatingSeries`, and `inner`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), reported for
  each of the six public theorems in the implementation seat's verification
  receipt. Stage-B did not rerun the axiom inspection.

## Triage

`theorem`. The formal proof closes the mod-five assertion for every positive
index; it does not claim to resolve every comment in the OEIS entry.

## ASSUMED-UNVERIFIED

The quotations, attribution, and date were supplied by the orchestrator and
recorded in the Library note. The OEIS revision history was read by the search
seat on 2026-09-08, not by this seat. The no-proof-found report is limited to
the OEIS entry/history and identifier searches on arXiv, MathOverflow, and
GitHub; it is not an exhaustive literature search or a first-publication
priority claim. Stage-B had no network access. Source-to-Lean identification,
external search results, and the orchestrator's exact check were not
independently verified by this seat.
