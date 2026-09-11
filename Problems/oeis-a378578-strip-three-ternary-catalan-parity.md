---
slug: oeis-a378578-strip-three-ternary-catalan-parity
bibkey: hanna2025a378578
doi: null
url: https://oeis.org/A378578
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity
---

# Strip-three ternary Catalan parity for A378578

## Problem

OEIS A378578 (Paul D. Hanna, Jan 03 2025) gives the following NAME and
COMMENT, quoted verbatim from `Library/Recurrence/hanna2025a378578.md`.

NAME:

> G.f. A(x) equals the series obtained by removing all factors of 3 from the coefficients in 1 + x*A(x)^3.

COMMENT:

> Conjecture: a(n) == binomial(3*n,n)/(2*n+1) (mod 2) for n >= 0.

The quotient is exact: these are the ternary Catalan numbers. The Lean
statement uses natural-number division; `ternary_catalan_div` records the
exact quotient identity for n > 0, with n = 0 handled directly.

## Motivation

This is a first-tier OEIS conjecture from the 2025 entry. KPI = open problems
resolved. The formal assertion covers every natural-number index.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and performing identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network access and did not
independently repeat those readings or searches. This is a bounded literature
search report, not a claim of exhaustive absence or first-publication priority.

## Route

`strip3 m = m / 3 ^ padicValInt 3 m` removes every factor of 3 (and maps zero
to zero). `strip3_mod_two` proves its image in ZMod 2 equals that of m,
because the removed power of 3 is odd. `strip3Series F` applies this operation
coefficientwise. Starting from 1, `approximation` iterates
Phi(F) = strip3Series (1 + X * F^3). The factor X makes this a degree
contraction: agreement below degree d becomes agreement below degree d+1.
The stabilized coefficients define `a` and `generatingSeries` A.

`generating_equation` proves A(0) = 1 and
A = strip3Series (1 + X * A^3), exactly the formal reading of the OEIS NAME:
"the series obtained by removing all factors of 3 from the coefficients in
1 + x*A(x)^3". `generating_unique` covers every B with constant coefficient
1 satisfying that equation.

Over ZMod 2 stripping disappears. The reduced series F = A-bar satisfies
F = 1 + X * F^3 and hence F = F^2 + X * F^4. Frobenius gives binary descent
of its coefficients. `choose_three_lucas`, using Lucas' theorem from
`Mathlib.Data.Nat.Choose.Lucas`, gives the recursions modulo 2:
C(3*(2r), 2r) = C(3r, r), C(3*(4r+1), 4r+1) = C(3r, r), and
C(3*(4r+3), 4r+3) = 0. Strong induction matches these recursions to the
reduced coefficients; `mod_two_identity` states
A-bar = sum over n of C(3n,n) X^n in ZMod 2.

For n > 0, `ternary_catalan_div` proves the exact natural division identity
C(3n,n)/(2n+1) = C(3n,n) - 2*C(3n,n-1), using
(2n+1)*C(3n,n-1) = n*C(3n,n) and a bound ensuring the subtraction does not
truncate. Thus `hanna_conjecture` proves
a(n) % 2 = (C(3n,n)/(2n+1)) % 2 for every n. At n = 0,
a(0) = 1 = C(0,0)/1 directly. The module has only Mathlib imports, no D5
import, and generality G.

## Falsifier

A natural-number index n at which a(n) and C(3n,n)/(2n+1) have different
parities would contradict the assertion. The orchestrator's exact check is
supporting evidence only; it does not replace the unbounded formal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companion theorems: `strip3_mod_two`, `generating_equation`,
  `generating_unique`, `choose_three_lucas`, `ternary_catalan_div`,
  `mod_two_identity`.
- All seven public theorems have std3 axioms: `propext`, `Classical.choice`,
  `Quot.sound`, as reported in the implementation seat's axiom output.
- The formal reading of "removing all factors of 3" is given by these exact
  definitions (in the module namespace, with `open PowerSeries`):

```lean
def strip3 (m : ℤ) : ℤ := m / 3 ^ padicValInt 3 m

noncomputable def strip3Series (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => strip3 (coeff n F))
```

## Triage

`theorem`. The formal proof closes the universal parity assertion quoted
from OEIS A378578, with the generating series constructed and characterized
by its defining equation and uniqueness.

## ASSUMED-UNVERIFIED

The quotations, attribution, and date were supplied by the orchestrator and
copied from the Library note. The OEIS revision history was read by the
search seat, not this seat. Literature scope was the OEIS entry and revision
history plus identifier searches on arXiv, MathOverflow, and GitHub on
2026-09-09; Stage-B had no network access. No exhaustive MathSciNet, zbMATH,
or third-party Lean ecosystem search was performed by this seat.
First-publication priority and source-to-Lean identification are not
kernel-checked facts. Numerical checks and earlier build results were
reported by the orchestrator or implementation seat, not rerun by Stage-B.
