---
slug: a156216-diagonalghost
bibkey: hanna2009a156216
doi: null
url: https://oeis.org/A156216/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.result
---

# Hanna's diagonal ghost-power integrality conjecture

## Problem

Paul D. Hanna's second comment in OEIS A156216, internal revision #3,
reads:

> More generally, if exp( Sum_{n>=1} C(n) * x^n/n ) equals a power series in x with integer coefficients, then exp( Sum_{n>=1} C(n)^n * x^n/n ) also equals a power series in x with integer coefficients (conjecture).

For a characteristic-zero field $K$ and $C:\mathbb N\to K$, put
$H_C=\sum_{n\ge1}C_nX^n/n$ and $F_C=\exp(H_C)$, interpreted formally.
The assertion is $F_C\in\mathbb Z[[X]]\Rightarrow
F_{(C_n^n)}\in\mathbb Z[[X]]$, with the rings of integer series understood
through the canonical embedding into $K[[X]]$.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| The sequence $C(n)$ | `claim` quantifies $K$, its field and characteristic-zero structures, and $C:\mathbb N\to K$ | Every binding field and sequence |
| $\sum_{n\ge1}C_nX^n/n$ | `logarithmicInput` has coefficient zero at zero and $C_n/(n:K)$ otherwise | Entry $C_0$ is unused |
| The formal exponential | `exponentialSum` substitutes the logarithmic input into `PowerSeries.exp K` | Ordinary coefficients; no analytic condition |
| Integer input coefficients | The antecedent is the existing `HannaLogarithmicPowerClosure.IntegralSeries` | Canonical integer image |
| $C(n)^n$ | The consequent uses the sequence $n\mapsto C_n^n$ | Index-dependent natural power |
| Integer output coefficients | The consequent uses the same `IntegralSeries` | No positivity or nonzero restriction |

The existing `HannaDiagonalDerivativeParity.step a 0` is used in the
private differential-equation proofs; the public claim retains the literal
formal exponential. No source clause is dropped.

## Motivation

The named external problem is preregistered in
https://github.com/the-omega-institute/trureturing/issues/21407.
The settling declaration is
`D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.result`.
The source note is `Library/RecurrenceComposition/hanna2009a156216.md`.
The admissible settlement is Proved, with
`admission_basis: open-problem-resolution (#21407; Proved)`.
There is no theory atom or coverage edge for this external problem.

## Gap

The integer Euler ledger of an integral input supplies signed divisor
ghosts. A fixed Hadamard power does not directly address the simultaneous
change of base and exponent from $C_{mp^s}^{mp^s}$ to
$C_{mp^{s+1}}^{mp^{s+1}}$. The proof handles this operation by local
prime-power congruences and reconstructs the literal output exponential.

## Route

Write the input's Euler ledger as $(b_d)_{d\ge1}$. The reused
`PrimitiveEulerLedger.unique_primitive_euler_ledger` gives its integer
coefficients and stable finite products. Formal differentiation identifies
$C_n=\sum_{d\mid n}d b_d$ for positive $n$.

For every prime $p$, $s\ge0$ and $m>0$, the new divisors in
$mp^{s+1}$ are divisible by $p^{s+1}$. Hence
$p^{s+1}\mid C_{mp^{s+1}}-C_{mp^s}$, even when $p\mid m$.
Mathlib's `SModEq.pow_pow_add_one`, applied in the private
`fermat_lift`, lifts Fermat's congruence. Base congruence and this lift give
$p^{s+1}\mid C_{mp^{s+1}}^{mp^{s+1}}-C_{mp^s}^{mp^s}$.

For an integer sequence $a$ satisfying these local congruences, prime
pairing in the Moebius numerator proves
$n\mid\sum_{d\mid n}\mu(d)a_{n/d}$. Its integer quotient is the output
Euler ledger. The coefficient recurrence for $Xf'=Lf$, with prescribed
constant coefficient, is unique in characteristic zero and identifies the
integer Euler series with the literal formal exponential.
All manipulations are finite in each coefficient.

## Falsifier

A counterexample would be a binding characteristic-zero field and sequence
whose input exponential has embedded integer coefficients while an output
coefficient does not. The universal theorem `result : claim` excludes that
case within Lean's accepted axiom closure. Numerical prefixes alone do not
exclude a counterexample beyond their bounds.

## Evidence

The kernel statement is `HannaDiagonalGhostPowerIntegrality.result` in
`D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.lean`.
Its only public definitions are `logarithmicInput`, `exponentialSum` and
`claim`. The Blueprint displays the full statement and the source expressions.

### Independent finite computation

[Published experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/8e7f1dcf75f89aa584f0667e326ea30a33ea09a0/docs/reports/oeis-a156216-hanna-diagonal-power-integrality).
The immutable script is `docs/reports/oeis-a156216-hanna-diagonal-power-integrality/check.py`;
its SHA-256 is `4a8078da8433455f65e9d9d52a52e0b1d35ee98ae09611d5d098317826a7f1f9`.
Python 3 execution of those immutable bytes exits 0 with final result
`ALL_CHECKS_OK`.
The exact tested scopes are: all 14 displayed A156216 coefficients in degrees
$0\ldots13$; Lucas ghosts in degrees $1\ldots40$; all $3125$ degree-five
integer input polynomials with coefficients in $\{-2,-1,0,1,2\}$ through
degree 24; all $625$ signed Euler ledgers on indices $1,\ldots,4$ with
exponents in that set through degree 40; 12 signed inputs with an independent
literal exponential computation through degree 24; and Fermat lifting for
$-30\le z\le30$, $p\in\{2,3,5,7,11\}$ and $1\le r\le4$.
These are computed results, not an unbounded proof.

### Escape audit

The unfinished audit is https://github.com/the-omega-institute/trureturing/issues/21518.
Its targets are the settling `result` and the published owner lemmas
`PrimitiveEulerLedger.ledgerProduct_succ` and
`PrimitiveEulerLedger.coeff_mul_eulerFactor_of_lt`, and the published owner
definition `HannaDiagonalDerivativeParity.step` (an additional audit target
under this delivery's brief; definitions are exempt from the theorem-only
SL-031 delta check).
No Reg registration or `declared_validated` status is asserted.
The missing evidence is a faithful typed realization and equivalence bridge,
variation, sensitivity and observational dependence for the exact statements.

## Triage

| Item | Status and evidence kind | Evidence |
| --- | --- | --- |
| The premise forces every positive-index $C_n$ to be an embedded integer divisor ghost | Proved; kernel-checked private lemma | `integral_input_ledger` constructs $b$ with $C_n=\sum_{d\mid n}d b_d$ in $K$ for every $n>0$ |
| Arbitrary signed divisor ghosts satisfy local Gauss congruences for every $m>0$, including $p\mid m$; diagonal self-powers preserve them | Proved; kernel-checked private lemmas | `divisor_ghost_gauss` and `diagonal_congruence`, composed in `result` |
| Every integer sequence satisfying the stated local Gauss condition has an integral literal exponential and an integer Moebius ledger | Proved; kernel-checked private lemmas | `gauss_moebius_divisible`, `gauss_has_ledger`, `gauss_exponential_integral` |
| Zero and negative ghosts and all binding characteristic-zero fields are included without positivity or analytic assumptions | Proved; kernel-checked theorem | The full statement of `result`; its only premise is input integrality |
| The finite checker ends `ALL_CHECKS_OK` | Computed | The immutable experiment and exact scopes in Evidence; exit 0 and matching script SHA-256 |
| Exhaustive literature priority, including the unread Du-Huang-Li paper | Open; literature reading boundary | The bounded literature screen in #21407; completeness is `ASSUMED-UNVERIFIED` |
| General index-dependent exponent transforms beyond $n$ | Open | No classification is asserted by `result` |

### What the settlement shows

Proved (kernel-checked `result`): the local congruence mechanism suffices
for the whole source claim and therefore includes its Lucas-sequence example.
Proved (kernel-checked private `integral_input_ledger`): integrality of the
ghosts is a consequence of input integrality; it need not be assumed.
Proved (kernel-checked private `divisor_ghost_gauss`): the local formulation
needs no coprimality condition on the positive multiplier $m$.

Open: a classification of other exponent sequences. The present theorem
settles no additional named conjecture. The OEIS coefficient recurrence and
its Lucas example are compatible with the proved universal assertion; no
other source theorem is claimed to depend on it. The finite OEIS values
listed in Evidence are computed, rather than separate Lean theorems.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are `ASSUMED-UNVERIFIED`.
The inspected source and the bounded screen in #21407 do not constitute an
exhaustive priority determination. The Du-Huang-Li 2003 original,
DOI `10.1016/S0022-314X(02)00025-2`, and the Newton-Euler paper,
DOI `10.1016/J.JNT.2005.05.004`, remain unread boundaries. The supporting
Dold-sequence survey is Byszewski-Graff-Ward, arXiv:2007.04031v4,
DOI `10.1112/blms.12531`; it is not the source of Hanna's conjecture.
