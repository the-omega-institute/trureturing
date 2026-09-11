---
slug: oeis-a355872-bilateral-theta-reversion-mod-sixteen
bibkey: hanna2022a355872
doi: null
url: https://oeis.org/A355872
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen
---

# Coefficient congruences for the A355872 bilateral theta reversion

## Problem

OEIS A355872 (Paul D. Hanna, Aug 09 2022), as quoted in
`Library/Recurrence/hanna2022a355872.md`, gives the NAME:

> G.f. A(x) satisfies: x = Sum_{n=-oo..+oo} (-x)^(n^2) * A(x)^((n-1)^2).

The single conjecture anchor of this dossier is the COMMENT:

> Conjecture: a(n) == 2 (mod 4) for n >= 1.

The entry also states two further conjectures:

> Conjecture: a(2*n-1) == 2 (mod 8) for n >= 1.
>
> Conjecture: a(2*n) == 6 (mod 8) for n >= 1.

The latter two are settled by the companion `hanna_conjecture_mod_eight`;
they do not create additional resolution anchors in this dossier.

## Motivation

This is a first-tier OEIS conjecture from the 2022 entry. The KPI is open
problems resolved: the resolution claim attaches to the first conjecture,
proved for every positive index by `hanna_conjecture`.

## Gap

The supplied search found no proof. The search seat read the OEIS entry and
revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those searches; absence of a proof within that scope
does not establish exhaustive literature coverage or publication priority.

## Route

The NAME's bilateral sum is formalised coefficientwise. For a zero-constant
series F, `bilateralTerm F j` is (-X) raised to j squared times F raised to
(j-1) squared, with natural absolute-value squares as Lean exponents.
`bilateralTerm_coeff_eq_zero` proves that index j contributes nothing at
degree N if `j.natAbs ^ 2 + (j - 1).natAbs ^ 2 > N`. Outside
`Finset.Icc (-(N : Int)) N`, j squared already exceeds N, so this finite
window is exact. Mathlib has no bilateral infinite sums of formal series;
the coefficientwise finite-window equation is the honesty boundary.

A is the stabilised fixed point of the degree-contracting operator
`2 * X - tail`, where the tail omits indices 0 and 1.
`generating_equation` proves A(0) = 0 and, for every N,
`coeff N X = sum_{j in Icc (-N) N} coeff N (bilateralTerm A j)`.
`generating_unique` identifies every zero-constant solution with A.
`support_one_mod_four` proves c(m) = 0 when m is not congruent to 1 modulo 4,
justifying the entry's indexing `a(n) = c(4*n-3)` for positive n.

`mod_sixteen_identity` identifies the reduction of A modulo 16 with
`2 * X * invOfUnit (1 + X ^ 4) 1`. The candidate's fourth power is zero,
so its tail collapses to X to the fourth power times the candidate. The
formal inverse identity and fixed-point uniqueness prove the result directly.
Coefficient comparison then gives `hanna_conjecture`: a(n) is congruent to
2 modulo 4 for every n at least 1. Only this theorem carries the resolution
claim. The companion `hanna_conjecture_mod_eight` proves a(2n-1) congruent
to 2 and a(2n) congruent to 6 modulo 8, settling the entry's two further
conjectures in prose without a second claim. There is no D5 import;
the module has generality G.

## Falsifier

A positive index n for which the specified series has a(n) not congruent
to 2 modulo 4 would falsify the anchored assertion. The orchestrator's
exact coefficient check is supporting evidence only; the theorem has no
finite index bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.lean`.
- Main theorem and sole resolution anchor: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`,
  `bilateralTerm_coeff_eq_zero`, `support_one_mod_four`,
  `mod_sixteen_identity`, `hanna_conjecture_mod_eight`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported
  for all seven public theorems by the implementation seat.

## Triage

`theorem`. The formal proof closes the universal first conjecture recorded
by OEIS; the two modulo-eight statements are companion results.

## ASSUMED-UNVERIFIED

The quotes were supplied by the orchestrator and copied from the Library
note. The OEIS revision history was read by the search seat, not by this
seat. Literature scope was the OEIS entry and revision history plus
identifier searches on arXiv, MathOverflow, and GitHub on 2026-09-09;
this seat had no network access. Source-to-Lean identification, exhaustive
literature coverage, and first-publication priority are not kernel-checked
facts. The orchestrator's exact check and external gate reports were not
independently rerun by this seat.
