---
slug: oeis-a396846-logarithmic-quarter-normalization-mod-eight
bibkey: hanna2026a396846
doi: null
url: https://oeis.org/A396846
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight
---

# The A396846 logarithmic coefficients modulo eight

## Problem

Paul D. Hanna, OEIS A396846, Jun 24 2026. The following NAME and COMMENT
are copied verbatim from the quotation in `Library/Recurrence/hanna2026a396846.md`:

> L.g.f. Sum_{n>=1} a(n)*x^n/n = log(1+x + Sum_{n>=2} 4*n/(4*n^2-1) * a(n)*x^n ).

> Conjecture: a(n) == [1,7,5,7] repeating (mod 8) for n >= 1.

This dossier resolves only the mod-8 conjecture. The entry's first conjecture,
"a(n) == 1 (mod 3) iff n is a power of 3, otherwise a(n) is divisible by 3",
is not resolved here.

## Motivation

This is a first-tier OEIS conjecture from 2026. KPI = open problems resolved.
The target is a universal residue classification at every positive index.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat those searches. That search scope does not establish exhaustive absence
of a proof.

## Route

The coefficients are constructed over the integers by well-founded recursion
for the integral normalization c_n = a(n)/(4n^2-1), for n >= 2.
`c_recurrence` gives c_n = a(n-1) + 4 Sum_{k=2}^{n-1} k c_k a(n-k),
and `a_eq` gives a(n) = (4n^2-1)c_n. The initial values are a(0)=0 and a(1)=1;
c(0)=c(1)=0, so the normalization formula is asserted only for n >= 2.

With H = 1 + X + Sum_{n>=2} 4n c_n X^n and B = Sum_{n>=1} a(n) X^n,
`log_derivative_identity` proves B H = X H'. After mapping to the rationals,
`coeff_H_rat` identifies H's coefficient at n >= 2 as
4n/(4n^2-1) a(n). Together these express the NAME formally. Mathlib has no
`PowerSeries.log`; the honesty boundary is the logarithmic-derivative identity
and exact rational coefficient shape, rather than a theorem using that operator.
The intended logarithm has zero constant coefficient and coefficient a(n)/n
at positive n.

`generating_unique` works over the rationals: any b and h with b(0)=0,
b(1)=1, h's constant and linear coefficients equal to one, the same rational
coefficient shape, and mk b * h = X * h' has b(n) = a(n) for every n.
`all_odd` follows from the integral recurrence. Oddness reduces the normalized
convolution modulo two to the sum of its indices; induction evaluates four
times that sum modulo eight. The final residue-count induction gives
`hanna_conjecture` as four conjuncts: n congruent to 1, 2, 3, 0 modulo four
implies a(n) congruent to 1, 7, 5, 7 modulo eight, respectively, for n >= 1.
The module has Mathlib-only imports, no D5 import, and generality G.

## Falsifier

A positive index n whose coefficient has a residue other than 1, 7, 5, 7
in the respective index classes 1, 2, 3, 0 modulo four would falsify the claim.
The orchestrator's exact numerical check is supporting evidence only; the
formal theorem has no finite index bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.lean`.
- Main theorem: `hanna_conjecture` (the four-conjunct form).
- Companions: `c_recurrence`, `a_eq`, `log_derivative_identity`, `coeff_H_rat`,
  `generating_unique`, `all_odd`.
- The two exact statements that read the NAME formally are:

```lean
theorem log_derivative_identity : B * H = X * derivative ℤ H

theorem coeff_H_rat (n : ℕ) (hn : 2 ≤ n) :
    coeff n (H.map (Int.castRingHom ℚ)) =
      (4 * n : ℚ) / (4 * (n : ℚ) ^ 2 - 1) * (a n : ℚ)
```

Mathlib has no `PowerSeries.log`; these statements give the derivative equation
and the rational coefficients of its argument. Single-file Lean validation
by Stage-B exited 0. All seven public theorems reported std3 axioms:
`propext`, `Classical.choice`, `Quot.sound`.

## Triage

`theorem`. The formal proof resolves the mod-8 conjecture for all positive
indices, with rational uniqueness identifying the constructed coefficients.

## ASSUMED-UNVERIFIED

The quotes and source metadata were supplied by the orchestrator through the
Library note and task brief. The OEIS revision history was read by the search
seat, not by this seat. The reported literature scope was the OEIS entry and
revision history plus identifier searches on arXiv, MathOverflow, and GitHub
on 2026-09-09; Stage-B had no network access. This does not certify exhaustive
literature coverage or first-publication priority. The source-to-Lean reading
and the orchestrator's exact numerical check are not kernel-checked source
facts. No resolution of the separate mod-3 conjecture is claimed.
