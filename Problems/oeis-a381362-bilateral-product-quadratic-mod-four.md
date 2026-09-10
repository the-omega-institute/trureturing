---
slug: oeis-a381362-bilateral-product-quadratic-mod-four
bibkey: hanna2025a381362
doi: null
url: https://oeis.org/A381362
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/BilateralProductModFour
---

# The A381362 bilateral product coefficient congruence

## Problem

OEIS A381362, Paul D. Hanna, Feb 21 2025:

NAME:

> G.f. A(x) satisfies 1/2 = Sum_{n=-oo..+oo} x^n*A(x)^n * (A(x)^n + x)^(2*n-1) * (x^n + A(x))^(2*n-1).

COMMENT:

> Conjecture: for n > 0, a(n) == 2 (mod 4).

OEIS A381363, Paul D. Hanna, Feb 21 2025:

NAME:

> G.f. A(x) satisfies 1/2 = Sum_{n=-oo..+oo} x^n*A(x)^n * (A(x)^n + x)^(3*n-1) * (x^n + A(x))^(3*n-1).

COMMENT:

> Conjecture: for n > 0, a(n) == 2 (mod 4).

This dossier resolves A381362, the `c = 2` instance, and cites its own Library note
`Library/ArithSums/hanna2025a381362.md`. The sibling quote records the shared family.
The generating series is normalized by `A(0) = 1`.

## Motivation

This is a first-tier OEIS conjecture from 2025. KPI = open problems resolved.
The general theorem covers every natural parameter `c ≥ 2` and every positive coefficient index.

## Gap

The search seat reported no proof found after reading the OEIS entry and revision history on
2026-09-09 and searching the identifiers on arXiv, MathOverflow, and GitHub.
This Stage-B seat has no network access and did not independently repeat those searches.
The report is bounded by that literature scope and does not establish publication priority.

## Route

The escape witness is the **general** theorem `hanna_conjecture_general`, covering every natural `c ≥ 2`: the normalized series defined by `1/2 = Σ_{n∈ℤ} xⁿ·Aⁿ·(Aⁿ + x)^{cn−1}·(xⁿ + A)^{cn−1}` has `a(n) ≡ 2 (mod 4)` for every `n > 0`. The two entry conjectures are its named instances at `c = 2` and `c = 3`; the instances themselves are not the escape witness.

The live path starts with `finite_window`, which makes the bilateral sum well defined coefficientwise. For the normalization `A(0) = 1`, the term at `n ≥ 1` has order `n`; at `n = −k`, `k ≥ 1`, the closed form `x^{ck²}·A^{ck²}·(1 + x·A^k)^{−ck−1}·(1 + x^k·A)^{−ck−1}` has order `c·k²`. Each coefficient therefore sees only finitely many indices; no infinite sum object is assumed. The normalized form `(1 + x)(1 + A)(1 − 2H) = 2` isolates the zero-index term. Contraction of the normalized bilateral terms constructs the integral solution and stabilizes its coefficients. `generating_equation` identifies its literal Laurent equation, and `generating_unique` proves uniqueness among normalized integer solutions. Deriving `1 + A = 2B` and then `A − (2/(1+X) − 1) = 4·B·H` yields the congruence.

Sibling fixed-point theorems in the repository specialize different equations and do not apply verbatim, so the minimal agreement and contraction helpers are re-proved privately. Target generality: `G`.

## Falsifier

A positive index `n` for the normalized A381362 series with `a(n) % 4 ≠ 2`
would falsify this entry's conjecture. More generally, any natural `c ≥ 2` and positive
index violating the congruence would falsify the general theorem's mathematical interpretation.
The orchestrator's exact finite check is supporting evidence only.

## Evidence

- Lean module: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.lean`.
- Main instance theorem: `hanna_conjecture_a381362` (`c = 2`).
- General escape theorem: `hanna_conjecture_general`.
- Companions: `finite_window`, `polynomial_form` (the normalized form),
  `generating_equation`, and `generating_unique`.
- Axioms: std3, exactly `[propext, Classical.choice, Quot.sound]`, as reported by the implementation seat.

The orchestrator reported the following readings from `results/verify-r19.out` as supporting evidence only, not proof: for both `c = 2` and `c = 3`, the coefficients are integral and the residual of the defining relation is zero through degree 24. The computed coefficients reproduce the published DATA exactly: `1, 2, 46, 862, 20414, 526106, 14519710` (A381362) and `1, 2, 66, 1986, 70750, 2773026, 115646874` (A381363). For each parameter, `a(n) ≡ 2 (mod 4)` holds for every `n` in `1..25`, with zero violations.

## Triage

`theorem`. The named instance proves the entry's universal positive-index assertion via the general family theorem.

## ASSUMED-UNVERIFIED

The OEIS quotes and metadata were supplied by the orchestrator and copied from the two Library notes.
The OEIS revision history was read by the search seat, not this seat. Literature scope was the
OEIS entry and revision history plus identifier searches on arXiv, MathOverflow, and GitHub;
no exhaustive literature or first-publication claim is made. Source-to-Lean identification
is not a kernel-checked fact. The readings attributed to `results/verify-r19.out` were supplied
by the orchestrator; this seat did not locate that file or independently run the computations.
