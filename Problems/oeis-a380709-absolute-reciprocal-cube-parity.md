---
slug: oeis-a380709-absolute-reciprocal-cube-parity
bibkey: hanna2025a380709
doi: null
url: https://oeis.org/A380709
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity
---

# Binomial parity of the A380709 coefficients

## Problem

Paul D. Hanna, OEIS A380709, Feb 09 2025. The following NAME and COMMENT
are quoted verbatim from the claim in `Library/Recurrence/hanna2025a380709.md`.

NAME:

> G.f. A(x) satisfies A(x) = 1 + x*abs( 1/A(x) )^3.

COMMENT:

> Conjecture: a(n) == binomial(4*n-1, n) (mod 2) for n >= 0 (cf. A263132).

Here abs is the series of coefficientwise absolute values, applied to the
reciprocal before cubing, as defined by the entry's formulas and the sibling
entries A380710/A383377. The positive-index assertion is `hanna_conjecture`.
At n = 0 the entry reads binomial(-1, 0) = 1; the companion `a_zero` proves
a(0) = 1. This reading does not use truncated natural subtraction to define
a generalized negative-upper-index binomial coefficient.

## Motivation

This is a first-tier OEIS conjecture from 2025. KPI = open problems resolved.
The module constructs the sequence and proves the assertion at every index,
using the stated separate reading at zero.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and performing identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those searches. The reported scope does not establish
exhaustive literature coverage or first-publication priority.

## Route

`absSeries F` is `mk (fun n => |coeff n F|)`. The private `approximation`
constructs A by stabilized iteration, starting at one, of
Phi(F) = 1 + X * (absSeries (invOfUnit F 1))^3. Inversion, absolute value,
and cubing preserve agreement below a degree; the factor X raises that
degree, making Phi a degree contraction. `generating_equation` states
A(0) = 1 and A = 1 + X * (absSeries (invOfUnit A 1))^3, exactly the NAME
with coefficientwise abs taken before cubing. `generating_unique` covers
every integer series B with constant coefficient one satisfying this equation.

Over ZMod 2 absolute values disappear. The reduced series F satisfies
F = 1 + X * F^(-3), so its reciprocal Q satisfies Q = 1 + X * Q^4.
For q(n) = C(4n+1,n) modulo two, `lucas_recursion_q` gives
q(4r+1) = q(r), q(4r+3) = 0, and q(2r) = [r = 0]. These Lucas recursions
and Frobenius show that the binomial series Q_q = sum q(n) X^n satisfies
the same quartic equation. The parity series
H = 1 + sum_{n >= 1} C(4n-1,n) X^n satisfies H = H^2 + X * Q_q^2,
again by Lucas and Frobenius. F satisfies the corresponding quadratic equation.
Unit-factor cancellation gives uniqueness for the quartic equation and for
the quadratic equation among series with constant coefficient one.
Consequently `mod_two_identity` identifies the reduction of A with H.

`a_zero` gives a(0) = 1, and `hanna_conjecture` gives
a n % 2 = C(4n-1,n) % 2 for every n > 0. The entry's zero-index reading
C(-1,0) = 1 is represented by `a_zero`. The module imports only Mathlib,
has no D5 import, and declares generality G.

## Falsifier

A positive index n whose constructed coefficient has parity different from
C(4n-1,n), or a constant coefficient different from one, would falsify the
assertion. The orchestrator's exact coefficient check is supporting evidence
only; it is not the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `lucas_recursion_q`,
  `mod_two_identity`, `a_zero`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for all six public
  theorems, as reported by the implementation seat's axiom checks.
- The exact Lean definition of coefficientwise absolute value is:

```lean
noncomputable def absSeries (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => |coeff n F|)
```

## Triage

`theorem`. The positive-index conjecture is proved by `hanna_conjecture`, and
`a_zero` supplies the entry's binomial(-1,0) = 1 reading at zero.

## ASSUMED-UNVERIFIED

The OEIS quotations, attribution, date, and coefficientwise interpretation
were supplied by the orchestrator. The search seat, not this seat, read the
OEIS revision history on 2026-09-09. The reported literature search covered
the entry and its history and identifier searches on arXiv, MathOverflow,
and GitHub; this seat had no network access. Source-to-Lean identification,
literature completeness, and first-publication priority are not kernel-checked
facts. The implementation seat supplied the std3 axiom report.
