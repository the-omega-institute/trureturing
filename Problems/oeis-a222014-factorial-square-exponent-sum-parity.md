---
slug: oeis-a222014-factorial-square-exponent-sum-parity
bibkey: hanna2024a222014
doi: null
url: https://oeis.org/A222014
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.hanna_conjecture
---

# Parity of the A222014 factorial square-exponent sum

## Problem

OEIS A222014 defines its generating series by

> A(x) = Sum_{n>=0} n! * x^n * A(x)^(n^2) / Product_{k=1..n} (1 + k*x*A(x)^n).

Paul D. Hanna's comment of Dec 06 2024 states, verbatim:

> Conjecture: a(n) is odd iff n = 2^k - 1 for some k >= 0.

The infinite sum is formalized coefficientwise by its exact finite window.

## Motivation

The requested first-tier theorem covers every natural index, including zero.
The listed coefficients have odd indices `0, 1, 3, 7, 15`, which is supporting
evidence rather than a substitute for the universal result.

## Gap

Repository searches found no A222014 declaration and no exponent-function
version of the required coefficient contraction. The closest result was the
established A222013 module, whose summand fixes the exponent to `r*(r+1)/2`.
Pinned Mathlib supplies power-series coefficient, unit inverse, divisibility,
and `ZMod 2` casting lemmas, but no theorem matching this recurrence or parity
classification was found in the searched scope.

## Route

`parameterizedTerm e d r F` is the product of `r!`, `X^r`, `F^(e r)`, and the
unit inverse of the product of `1 + (k+1)*X*F^(d r k)` over `k < r`. The theorem
`parameterized_term_coeff_eq_zero` is uniform in both exponent functions:
the explicit `X^r` factor alone makes coefficient `N` vanish whenever `N < r`.
Consequently no monotonicity or lower-bound hypothesis on `e` or `d` is needed.
The triangular choices `e(r)=r(r+1)/2`, `d(r,k)=k+1` recover A222013 by
definitional equality, while `e(r)=r^2`, `d(r,k)=r` give A222014.

Stabilized finite-window iteration constructs the integer coefficient sequence.
`generating_equation` states the exact coefficientwise equation and
`generating_unique` proves uniqueness by degree contraction.

Modulo two, divisibility of `r!` by two removes all terms with `r >= 2`.
The remaining two terms imply `C = 1 + X*C^2`. This equation and constant
coefficient one identify the reduced A222014 series with the reduced A222013
series. `mod_two_identity` and `hanna_conjecture` then invoke the corresponding
A222013 theorems directly.

The target has generality I because its same-level import is the instance-level
module `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity`.

## Falsifier

A natural index whose A222014 coefficient has oddness different from membership
in `{2^k - 1 : k >= 0}` would contradict the theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.lean`.
- Resolution anchor: `hanna_conjecture`.
- General contraction: `parameterized_term_coeff_eq_zero`.
- Companions: `term_coeff_eq_zero`, `generating_equation`, `generating_unique`,
  `mod_two_equation`, and `mod_two_identity`.
- Directed dependency: `FactorialSquareExponentSumParity.hanna_conjecture` to
  `FactorialProductSumCatalanParity.hanna_conjecture`.
- All seven public theorems use only `propext`, `Classical.choice`, and
  `Quot.sound`.

The exact final statement is:

```lean
theorem hanna_conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k
```

## Triage

`theorem`. The formal proof closes the universal parity assertion recorded by
OEIS.

## ASSUMED-UNVERIFIED

The defining equation, conjecture, attribution, date, and numerical check were
supplied by the implementation brief. Source-to-Lean identification and
publication priority are not kernel-checked facts.
