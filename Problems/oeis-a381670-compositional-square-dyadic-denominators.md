---
slug: oeis-a381670-compositional-square-dyadic-denominators
bibkey: scheuerle2025a381670
doi: null
url: https://oeis.org/A381670
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators
---

# Dyadic denominators of the A381670 compositional-square series

## Problem

OEIS A381670 (Thomas Scheuerle, Mar 03 2025), NAME, as quoted in
`Library/ArithSums/scheuerle2025a381670.md`:

> The function A(x) = x+(1/2)*x^2-(1/16)*x^4... = Sum_{k >= 0} x^k*A381669(k)/a(k) satisfies the functional equation: x*(A(x)+1) = A(A(x)).

The COMMENT that is the target, from the same Library note:

> Conjecture: All terms are powers of two.

The brief separately supplied the purported comment:

> All terms appear to be odd.

That sentence does not occur in the supplied Library note. It cannot describe
these denominators: the displayed coefficient of x^2 has denominator 2.
Its attribution is unverified, and it is not a second resolution claim.

## Motivation

This is a first-tier OEIS conjecture from the 2025 entry. The KPI is open
problems resolved. The target module proves the denominator assertion at
every natural-number index, including indices with a zero coefficient.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did
not independently repeat those readings or searches.

## Route

The delivered escape content is the integral rescaling F(x)=A(4x)/4.
For approximations tangent to X, changing degree n by c changes the same
degree of the compositional-square residual by exactly 2c. If P-X is
divisible by 2, then P(P)-X-4XP is divisible by 4. Its negative half is
therefore an even correction. Induction proves coefficient stabilization
and preserves evenness; the stable integral series satisfies its equation.
Undoing the scaling proves the rational functional equation, and triangular
coefficient induction proves uniqueness.

The theorem `rescaled_even` states that 4^(n-1)f(n) is an even integer for
n >= 2. It is a supporting lemma used by `scheuerle_conjecture`, which
deduces that the reduced denominator divides 4^(n-1), hence is a power of
two. It is not an oddness corollary or a second open-problem resolution.

Only Mathlib is imported, so generality is G and there are no direct frozen
D5 dependencies. The implementation seat recorded that the frozen public
fixed-point theorem concerns a different operator; the required private
agreement and stabilization lemmas were re-proved.

## Falsifier

A natural index k whose reduced denominator (f k).den is not 2^e for any
natural e would falsify the target. The orchestrator's reported exact
finite check is supporting evidence only, not the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.lean`.
- Main theorem: `scheuerle_conjecture`.
- Companions: `functional_equation`, `uniqueness`, and the supporting
  even-integrality theorem `rescaled_even`.
- All six public declarations report std3 axioms:
  `[propext, Classical.choice, Quot.sound]` in the implementation log.
- The public theorem quantifies over every natural index, including zero
  coefficients, whose denominator is one.

## Triage

`theorem`. The formal proof closes the universal denominator assertion
recorded in the supplied OEIS quotation.

## ASSUMED-UNVERIFIED

The quotes were supplied by the orchestrator; the NAME and target COMMENT
match the Library note. The oddness quote does not. The OEIS revision
history was read by the search seat, not this seat. The reported literature
scope was identifier search on arXiv, MathOverflow, and GitHub; absence of
a proof in that scope does not establish first-publication priority.
Source-to-Lean identification is not a kernel-checked fact.

The brief also supplied a route using A=X·U, X²·U cancellation, a contracting
operator, two homogenized polynomial identities, and the classification
`a n % 4 = if n % 6 = 3 then 3 else 1` for n > 0. Those constructions and
that classification do not occur in this module. The accompanying claim
that two entry clauses cover all 39 computed positions was not independently
verified and is not evidence for this module's denominator theorem. Both
classification residues are odd, but no such classification or derived
oddness corollary is claimed here. The delivered `rescaled_even` is proved
before, and used by, `scheuerle_conjecture`.
