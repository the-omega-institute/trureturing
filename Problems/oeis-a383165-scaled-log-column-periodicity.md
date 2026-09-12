---
slug: oeis-a383165-scaled-log-column-periodicity
bibkey: bala2026a383165
doi: null
url: https://oeis.org/A383165
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity
---

# Eventual periodicity of OEIS A383165

## Problem

The entry-specific Library note `Library/ArithSums/bala2026a383165.md`
records the NAME and conjecture verbatim as follows:

> Expansion of e.g.f. log(1 + (exp(2*x) - 1)/2)^2 / 2.

> Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic.

The note attributes the entry to Seiichi Manyama (April 18, 2025) and the
conjecture to Peter Bala (February 17, 2026). This dossier claims only this
entry's eventual-periodicity conjecture, not a divisibility clause of a
negative-power diagonal family. The claimed conclusion is existence of an
onset and a positive period, without a specified or minimal period.

## Motivation

This is a first-tier OEIS conjecture: entry year 2025, conjecture year 2026,
as recorded in its own Library note. KPI = open problems resolved. The
formal theorem treats every natural column and every positive modulus.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and performing identifier searches on arXiv,
MathOverflow, and GitHub. This seat had no network and did not independently
repeat those searches. The supplied negative-power quotes conflict with the
Library notes, so the search report does not establish priority for the
formalized statement without source reconciliation.

## Route

The escape content is the private `scaled_bridge`, which proves
`W(n,r,j) = n!·coeff(n, H^(−j)·(log H)^r / r!)` with
`H = 1 + (exp(2X) − 1)/2` by induction through a new integral differential
system. `W_congr` and `state_step` close that recurrence on finitely many states
modulo `m`; `state_period` and `W_period` yield eventual periodicity for every
positive modulus. `a_eq` transfers this result to the defined coefficients.

This is not an instance of the repository's frozen totient-period theorem:
the supplied comparison says that theorem and its bridge require an INTEGER
weight and substitution `exp x − 1`. Here the substitution is `exp 2x − 1`,
and the outer function `log(1 + y/2)^r / r!` is not integral: its coefficients
carry powers of two and factors of the coefficient index `j` in denominators.
Rescaling gives `2^n` times a transform of rational weights, with `2^n` varying
with `n`. This comparison is supplied context, not a frozen-dependency audit.
The module imports only Mathlib and has generality G; no frozen D5 theorem
lies on its proof path.

The escape witness supports the general theorem `coefficient_periodicity`,
quantified over every natural column `r` and every positive modulus `m`.
It therefore covers every prime modulus `p`, and is not merely the two named
instances. A383165 and A383166 are DIFFERENT sequences (columns `r = 2` and
`r = 3`) sharing one conjecture sentence; this single theorem over `r` implies
both. The delivered proof uses differential states and finite-state repetition.
It contains no residual-vanishing argument or `Nat.choose_mul_right` identity,
no Lucas theorem, and no prime-power case analysis. The brief's requested
prime-divisibility explanation is unsupported by this module.

## Falsifier

For a proposed onset `N` and positive period `p`, a counterexample index
`n ≥ N` with unequal residues `a 2 (n+p)` and `a 2 n` falsifies that
candidate. To refute eventual periodicity requires a positive modulus for
which every proposed `N,p` has such an index. A finite exact check alone
cannot prove or disprove existence of some eventual period.

## Evidence

- Lean module: `D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity.lean`.
- Entry-specific public theorem: `bala_conjecture_a383165`.
- Companions: `generating_equation` and the general theorem `coefficient_periodicity`.
- Single-file Lean verification by this seat: exit 0. All five public
  declarations report std3: `[propext, Classical.choice, Quot.sound]`.
- The named theorem specializes the general theorem at `r = 2`.

The orchestrator's supporting readings come from `results/verify-r25.py` and its
receipt `results/verify-r25.out`, computed in exact rational arithmetic to `n < 70`
with the coefficients taken from the entries' own exponential generating function:

- both columns are integral throughout that range;
- A383165 reproduces its published DATA exactly for the first fourteen terms:
  0, 0, 1, 3, 3, -10, -30, 112, 588, -2448, -18960, 87296, 911328, -4599296;
- A383166 reproduces its published DATA exactly for the first fifteen terms:
  0, 0, 0, 1, 6, 15, -15, -210, 28, 5292, 4140, -208560, -369864, 11847264, 33630688;
- each entry's own modulo-5 example holds with zero violations, period 20 from
  `n = 3` for A383165 and from `n = 4` for A383166, over 47 and 46 indices;
- a sweep of `m = 2..12` found smallest periods 1 for the powers of two, 6 for 3,
  20 for 5, 42 for 7 and 18 for 9. No period up to 44 was found for `m = 11`,
  which is a limitation of the computed window and NOT a counterexample.

These are supporting computations only, not proof. The formal theorem asserts the
existence of an onset and a positive period; it claims no minimality, and none of
the measured periods above is asserted as proved.

ERRATUM, recorded deliberately. An earlier draft of this dossier carried, in this
section, the DATA arrays and defining relations of a DIFFERENT lane (the
negative-power diagonal family, A266489 and A395833), because this lane's Stage-B
brief was derived from that lane's and the substitution replaced identifiers
without replacing the mathematics. The Stage-B seat detected the inconsistency on
its own, observing that the delivered formal columns have constant term zero while
those arrays begin with one, and refused to rely on them. The review seats then
found that the disclaimed text still survived in this file. Both are recorded here
rather than silently deleted, because a reader deciding how much to trust these
numbers should know they were once wrong and how that was caught.

## Triage

`theorem`. The formal proof closes the eventual-periodicity conjecture for this
entry for every positive modulus, as the named instance of a theorem quantified
over every column `r`.

## ASSUMED-UNVERIFIED

The verbatim NAME and the conjecture sentence were supplied by the orchestrator
from the OEIS text endpoint; this seat had no network. The entry is by Seiichi
Manyama (Apr 18 2025) and the conjecture is by Peter Bala (Feb 17 2026); those
attributions are orchestrator-supplied and are recorded separately in the Library
note. The numerical readings above were computed by the orchestrator and are
supporting evidence only, not proof; this seat did not recompute them. No claim
is made that any period above is least, nor that the literature search was
exhaustive. Scribe C# compilation, emission and the repository admission gates
were run outside this seat's sandbox.
