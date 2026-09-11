---
slug: oeis-a380708-absolute-reciprocal-square-fibbinary-parity
bibkey: hanna2025a380708
doi: null
url: https://oeis.org/A380708
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity
---

# Fibbinary parity of the A380708 coefficients

## Problem

OEIS A380708, Paul D. Hanna, Feb 08 2025, gives the following NAME and COMMENT,
quoted verbatim from `Library/Recurrence/hanna2025a380708.md`:

> G.f. A(x) satisfies A(x) = 1 + x*abs( 1/A(x) )^2.

> Conjecture: for n > 0, a(n) is odd iff n = 2*A003714(k) + 1 for k >= 0, where A003714 are the fibbinary numbers.

Here abs means coefficientwise absolute value of the reciprocal, taken before
squaring, as defined in the sibling entries A380709/A380710. A003714 enumerates
the nonnegative integers with no two adjacent 1s in their binary expansion.
The frozen public predicate is `Fibbinary f := f &&& (f >>> 1) = 0`.

## Motivation

This is a first-tier OEIS conjecture from the 2025 entry. The KPI is open
problems resolved. The target proves the assertion for every positive index.

## Gap

No proof was found in the supplied search: the search seat read the OEIS entry
and revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network access and did not
repeat those searches. This is a bounded literature search, not a priority proof.

## Route

`absSeries` is the frozen public definition from
`D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity`, reused by import
and never redeclared. The integer series A is the stabilized fixed point of
`Phi(F) = 1 + X * (absSeries (invOfUnit F 1)) ^ 2`. Absolute value is taken
before squaring; multiplication by X gives degree contraction. Thus
`generating_equation` states A(0) = 1 and exactly the NAME's equation, and
`generating_unique` covers every integer series B with constant coefficient 1
satisfying that equation.

Over ZMod 2 absolute value disappears. Writing F for the reduction of A,
its reciprocal B satisfies `B = 1 + X * B^3`. Factoring the difference of two
solutions and cancelling a unit identifies B with the reduction of the frozen
`D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.generatingSeries`.
The latter reduced series has degree-k coefficient `C(3k,k)` modulo 2;
it is the series `sum_k (C(3k,k) mod 2) X^k`. Frobenius then gives
`mod_two_identity`: the reduction of A is `1 + X * expand 2` of that series.

`choose_three_odd_iff` matches the Lucas recursions of `C(3f,f)` modulo 2
from the frozen `choose_three_lucas` with the bit recursions of the frozen
public `Fibbinary` predicate from
`D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity`, by strong
induction. Hence `hanna_conjecture` proves, for n > 0,
`Odd (a n) <-> exists f, Fibbinary f and n = 2*f + 1`, which is the COMMENT's
`n = 2*A003714(k) + 1`. Target generality is I because the proof imports these
three frozen providers; `AbsoluteReciprocalSquareParity` is itself of
generality I, while `FibbinarySquareSubstitutionParity` and
`StripThreeTernaryCatalanParity` are G.

## Falsifier

A positive index n whose coefficient is odd without n = 2f + 1 for a fibbinary
f, or whose coefficient is even despite that representation, would contradict
the assertion. The orchestrator's exact finite check is supporting evidence
only; it does not establish the universal result.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_identity`,
  `choose_three_odd_iff`.
- The implementation seat reported axioms std3 for all five public theorems:
  `propext`, `Classical.choice`, `Quot.sound`.
- The exact generating equation in Lean is:

```lean
theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = 1 + X * (absSeries (invOfUnit generatingSeries 1)) ^ 2 := by
```

## Triage

`theorem`. The formal proof closes the universal positive-index assertion
recorded in OEIS A380708.

## ASSUMED-UNVERIFIED

The OEIS quotes, date, and sibling-entry interpretation were supplied by the
orchestrator. The search seat read the OEIS revision history on 2026-09-09;
this seat did not. The literature scope was the entry, revision history, and
identifier searches on arXiv, MathOverflow, and GitHub. No exhaustive search
of private literature indexes or first-publication priority is claimed.
The identification of the source text with the formal statement is not a
kernel-checked fact. This seat used no network access.
