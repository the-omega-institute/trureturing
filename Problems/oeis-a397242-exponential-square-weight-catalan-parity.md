---
slug: oeis-a397242-exponential-square-weight-catalan-parity
bibkey: hanna2026a397242
doi: null
url: https://oeis.org/A397242
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity
---

# Parity of the A397242 coefficients

## Problem

OEIS A397242, Paul D. Hanna, Jun 19 2026, gives the following NAME and first
COMMENT, quoted from `Library/Recurrence/hanna2026a397242.md`:

> O.g.f. satisfies A(x) = exp( x + Sum_{n>=2} (n^2-1) * a(n)*x^n / n^2 ).

> Conjecture: a(n) is odd iff n+1 is a power of 2.

The formal reading is `A(0)=1` and `X*A' = M*A`, where
`M = X + sum_{n>=2} (n^2-1) a(n) X^n / n`. The integral normalization
`d(n) = a(n)/n` for positive n realizes these weights. The entry's two other
comments conjecture classifications modulo 3; neither is resolved here.
This dossier makes one resolution claim, on `hanna_conjecture` alone.

## Motivation

This is a first-tier OEIS conjecture from 2026. The KPI is open problems
resolved: the first parity conjecture, quantified over every natural index.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat that search. Absence of a discovered proof is bounded by that scope.

## Route

The escape content is the integral normalization `d(n) = a(n)/n` for n >= 1,
with `d(1) = 1`. The theorem `d_recurrence` gives, for n >= 2,
`d(n) = (n-1)d(n-1) + sum_{j=2}^{n-1} (j^2-1)(n-j)d(j)d(n-j)`.
The theorem `a_eq` gives `a(n) = n*d(n)` for n >= 1, and the definition sets
`a(0) = 1`. Thus `M = X + sum_{n>=2} (n^2-1)d(n)X^n` is integral.

The theorem `log_derivative_identity` proves `A(0)=1` and `X*A'=M*A`.
The theorem `coeff_M_rat` identifies M's rational coefficients as
`(n^2-1)*a(n)/n`, namely X times the derivative of the exponent in the NAME.
This differential identity is the formal reading of the exponential equation.
The supplied API search found no Mathlib PowerSeries exp/log identity of this
shape; no separate exponential-substitution identity is proved. This is the
honesty boundary. The theorem `generating_unique` over Q proves that any b
satisfying the same constant terms, exact rational weight shape, and
differential equation equals a coefficientwise.

Over `ZMod 2`, the convolution at even indices vanishes, giving
`d(2m)=d(2m-1)` for m >= 1. Pairing the odd-index convolution yields the
Catalan recurrence for `d(2m+1)`. The theorem `mod_two_catalan` identifies
`X * (sum_m d(2m+1) X^m)` with the reduction of the frozen binary Catalan
series K of `Invariants/CatalanCompositionSquareParity`, using its
`catalan_equation`. Its `binary_catalan` support theorem then gives
`hanna_conjecture`: for every n, `Odd (a n) <-> exists k, n + 1 = 2^k`,
including n = 0. This resolves only the FIRST conjecture; the two mod-3
conjectures are not resolved. Target generality is I because the proof imports
the frozen `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`, itself G.

## Falsifier

A natural index n for which `Odd (a n)` differs from the assertion that
`n+1` is a power of 2 would contradict the theorem. The orchestrator's exact
check is supporting evidence only, not the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `d_recurrence`, `a_eq`, `log_derivative_identity`, `coeff_M_rat`,
  `generating_unique`, `mod_two_catalan`.
- Exact formal NAME evidence:

```lean
theorem log_derivative_identity :
    coeff 0 (mk a) = 1 ∧ X * derivative ℤ (mk a) = M * mk a

theorem coeff_M_rat (n : ℕ) (hn : 2 ≤ n) :
    coeff n (M.map (Int.castRingHom ℚ)) =
      ((n : ℚ) ^ 2 - 1) * (a n : ℚ) / n
```

- These statements prove the differential reading, not a literal exp identity.
- The implementation-seat envelope reports std3 for all seven public theorems:
  `[propext, Classical.choice, Quot.sound]`.
- Frozen dependency statement_id:
  `sha256:0033f4a50a501546a5f332ce1203c8cf1a936428e7a155a06a0443bb0f0f6232`.

## Triage

`theorem`. The formal proof resolves the universal first parity conjecture
under the differential reading of the NAME described above.

## ASSUMED-UNVERIFIED

The source quotes and attribution were supplied by the orchestrator. The OEIS
revision history was read by the search seat, not by this seat, which had no
network access. The reported literature search covered the OEIS entry and
history and identifier searches on arXiv, MathOverflow, and GitHub; it was not
an exhaustive literature or priority certification. Source-to-Lean
identification and first-publication priority are not kernel-checked facts.
The two mod-3 conjectures remain outside this resolution claim.
