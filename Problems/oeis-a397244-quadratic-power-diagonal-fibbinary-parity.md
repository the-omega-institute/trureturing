---
slug: oeis-a397244-quadratic-power-diagonal-fibbinary-parity
bibkey: hanna2026a397244
doi: null
url: https://oeis.org/A397244
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity
---

# Fibbinary parity of the A397244 coefficients

## Problem

OEIS A397244, Paul D. Hanna, gives the following NAME and Fibbinary COMMENT,
quoted verbatim from `Library/Recurrence/hanna2026a397244.md` and matched to
`oeis-A397244.src` supplied by the orchestrator:

> G.f. A(x) satisfies (2*n) * [x^n] A(x)^(2*n) = (2*n-1) * [x^n] A(x)^(2*n+1) for n > 1.

> Conjecture: for n > 0, a(n) is odd iff n = 2*A003714(k) + 1 for some k >= 0, where A003714 lists the Fibbinary numbers.

The initial values are a(0)=a(1)=1. A003714 enumerates the nonnegative
integers with no adjacent binary ones; the frozen public predicate is
`Fibbinary f := f &&& (f >>> 1) = 0`.

## Motivation

This is a first-tier OEIS conjecture in the recent-entry intake. The KPI
counts open problems resolved, not modules. The target is the assertion
for every positive index, not a finite test of its support.

## Gap

No proof was found in the supplied entry snapshot: it carries no references
and only a b-file link. This seat's inspection was offline and confined to
the supplied files. This seat did not search the literature. The
orchestrator's checks are numerical, not a literature search or a priority
proof; absence of a supplied proof does not establish absence in the literature.

## Route

For n > 1, let P be the strict prefix through degrees j < n. The recurrence
`a n = (2*n-1)*coeff n (P^(2*n+1)) - (2*n)*coeff n (P^(2*n))`
uses no a(n) on its right side and makes the definition non-circular.
The frozen diagonal multiplier proves the full-series equations. Modulo two,
the relation becomes `coeff n (S^(2*n+1)) = 0` for n > 1.

The escape is the new general lemma even_power_diagonal:
`∀ F : PowerSeries (ZMod 2), ∀ n > 0, coeff n (F^(2*n)) = 0`.
Frobenius descent writes `F^(2*n) = (F^n)^2`: odd n gives zero, while
n = 2*m descends to the same statement at m. With it, cubic_diagonal turns
`B^3 = B^2 + X` into `coeff n (B^(2*n+1)) = 0` for n > 1.
Thus the frozen candidate satisfies A397244's own equations and initial
coefficients. The general uniqueness argument underlying generating_unique
forces equality of the mod-two reductions: the Lean call is to the private
commutative-ring lemma equation_unique, whereas the public generating_unique
is its integer specialization. Coefficient parity then transports from the
frozen AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture.
The source-formula erratum and precise input boundary are in the library note.

## Falsifier

For n > 0, an odd a(n) with either n even or (n-1)/2 not Fibbinary, or an
even a(n) with n odd and (n-1)/2 Fibbinary, would refute the assertion.
The condition n odd is necessary when using natural-number division;
equivalently the support condition is existence of Fibbinary f with n=2*f+1.
The orchestrator's finite check is supporting evidence only.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.lean`.
- Public theorems: a_two, generating_equation, generating_unique,
  mod_two_cubic, mod_two_identity, hanna_conjecture_a397244.
- The implementation seat reports exactly axioms std3 for each theorem:
  propext, Classical.choice, Quot.sound.
- The six complete Lean statements are retained in the PR body draft.

## Triage

`theorem`. The formal proof closes the universal positive-index parity
assertion recorded in OEIS A397244.

## ASSUMED-UNVERIFIED

The quotes were supplied by the orchestrator from oeis-A397244.src; this
seat has no network and did not read OEIS or any literature. The
orchestrator's degree-256 computations were not rerun here. Identification
of the prose conjecture with the formal statement is not kernel-checked.
The erratum's %F(4) composition direction is unverified; none of %F(2),
%F(3), or %F(4) is a premise of the proof. No exhaustive literature search
or first-publication priority is claimed.
