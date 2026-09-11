---
slug: oeis-a392525-cubic-fifteen-substitution-parity
bibkey: hanna2026a392525
doi: null
url: https://oeis.org/A392525
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
---

# Parity of the A392525 coefficients

## Problem

OEIS A392525 (Paul D. Hanna, Jan 15 2026) gives the following NAME,
FORMULA (1), and COMMENT. The quotations are copied from the claim in
`Library/Arith/hanna2026a392525.md`; the attribution and date were supplied
by the orchestrator.

NAME:

> G.f. satisfies: A(x) = A( x^3 + 15*x*A(x)^3 )^(1/3), with A(0)=0, A'(0)=1.

FORMULA (1):

> (1) A(x)^3 = A( x^3 + 15*x*A(x)^3 ).

COMMENT:

> Conjecture: a(n) is odd iff n = 2^k for k >= 0.

### 范围与诚实边界

The module formalizes FORMULA (1) over integer formal power series with
`A(0)=0` and `A'(0)=1` (constant coefficient zero and linear coefficient one).
It does not formalize the cube-root operation in the NAME. The public parity
theorem is stated for every `n ≥ 1`; at `n = 0` the normalization gives `a(0)=0`,
and zero is not a power of two. The separate second comment,
`a(n) ≡ 5 mod 10 iff n = 2^k, k ≥ 1`, is not resolved here.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems resolved,
not the number of modules or finite coefficient checks. The target is the
unbounded parity assertion for the normalized generating series.

## Gap

The supplied search evidence reports no proof found: the search seat read the
OEIS entry and revision history on 2026-09-08 and searched the identifier on
arXiv, MathOverflow, and GitHub. This Stage-B seat had no network access and
did not repeat those searches. This is a bounded literature search, not a
proof of absence of prior work.

## Route

Integer existence is proved by exact coefficient corrections and stabilization.
Mathlib's Frobenius expansion modulo three makes every division by three exact.
The multiplicity-three first-difference formula and strong induction prove
uniqueness (`generating_equation`, `generating_unique`).

Over `ZMod 2`, the series `C = Σ x^{2^j}` (`powerTwoSeries`) satisfies
`C + C² = x` and `C³ = C.subst(X³ + X·C³)` (`thue_series_equation`). The cubic
identity follows by quadratic uniqueness: two zero-constant solutions obey
`(u−v)(1+u+v)=0`, and the second factor has constant coefficient one, so no zero
divisors forces equality.

Reducing the proved integer equation modulo two and applying the reduced
uniqueness theorem gives `A ≡ C`. Thus `a(n)` is odd exactly when `n = 2^k`
(`hanna_conjecture`). The module has only Mathlib imports, no D5 import or
frozen D5 prerequisite, and declares generality `G`.

## Falsifier

A positive index `n` at which `a(n)` is odd but `n` is not a power of two, or
at which `n` is a power of two but `a(n)` is even, would contradict the
assertion. The orchestrator's exact coefficient check is supporting evidence
only; no finite check establishes the universal theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `thue_series_equation`.
- Axioms: std3, exactly `propext`, `Classical.choice`, `Quot.sound` for each
  public theorem, as reported by the implementation seat's `#print axioms`.
- The theorem is quantified over all positive natural-number indices; the
  exact finite computations supplied by the orchestrator are supporting checks.

## Triage

`theorem`. The formal proof closes the parity assertion for the normalized
integer solution of FORMULA (1), within the scope stated above.

## ASSUMED-UNVERIFIED

The OEIS quotations, attribution, and date were supplied by the orchestrator;
the quotations were checked against the local Library note. The OEIS revision
history was read by the search seat on 2026-09-08, not by this Stage-B seat.
The literature scope was the OEIS entry and revision history plus identifier
searches on arXiv, MathOverflow, and GitHub; no exhaustive literature or
first-publication-priority claim is made. Source-to-Lean identification and
literature status are not kernel-checked facts. This seat had no network access.
