---
slug: cigler-narayana-strip-product
bibkey: cigler2026narayana
doi: 10.48550/arXiv.2608.03363
url: https://arxiv.org/abs/2608.03363v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.result
---

# A Product Formula for Narayana Strip Series of Heights 4m and 4m + 1

## Problem

Johann Cigler, *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana
polynomials for q=-1*, arXiv:2608.03363v2, Section 4, Conjecture 2, equation (79) (Conjecture 1, equation (62), in
v1): for m ≥ 1,

C^{(4m)}(t², z²) = c^{(4m)}(t, z) c^{(4m)}(−t, −z),  C^{(4m+1)}(t², z²) = c^{(4m+1)}(t, z) c^{(4m+1)}(−t, −z).

Here C^{(h)}(t, z) = Σ_n C_n^{(h)}(t) zⁿ and c^{(h)}(t, z) = Σ_n c_n^{(h)}(t) zⁿ, where C_n^{(h)}(t) and c_n^{(h)}(t) are
the weighted counts of Dyck paths of semilength n in the strip 0 ≤ y ≤ h, a down-step to height k having weight
τ_k with τ = (1, t, 1, t, …) and τ = (1, t, −1, −t, …) respectively. The identity is the bounded analogue of the
unrestricted identity c(t, z) c(−t, −z) = C(t², z²), equation (6) of the source.

## Motivation

The theorem `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.result` establishes both identities for every
m ≥ 1, coefficientwise in z over ℤ[t].

## Gap

Pre-registration issue 12527 records the literature screen: the arXiv record lists the identity as a conjecture
in v1 and v2, and searches of the identifier, of the formula and of the related finite-height continued-fraction
literature found no proof. This is a bounded negative finding.

## Route

1. The first-return decomposition expresses each bounded series as a quotient p_{h+1}/q_{h+1} of continuants, the
   denominator having constant term 1 in z.
2. The weights repeat with period four, so the continuants advance by a fixed 2 × 2 transfer block with trace
   1 − (1 + t²)z² and determinant t²z⁴; by the Cayley–Hamilton theorem every residue class of continuants satisfies
   the same second-order recurrence.
3. Addition and doubling identities for that recurrence give closed endpoint formulas for the q = −1 continuants
   and for the Narayana continuants, with separate terminal blocks for heights 4m and 4m + 1.
4. The numerators and the denominators factor separately; dividing by denominators with constant term 1 gives the
   identity of power series.

## Falsifier

The statement would fail if a terminal block were misaligned with the height, or if the numerator and denominator
factorizations held only up to a common factor.

## Evidence

An independent referee implementation checked both identities coefficientwise for 0 ≤ m ≤ 12 through z^48 by
direct path recursion, and the full polynomial factorizations for m ≤ 24.

## Triage

`theorem`; the statement is Conjecture 2 of arXiv:2608.03363v2 and is quantified over every m ≥ 1.

- Proved (formalized): both product identities for heights 4m and 4m + 1, every m ≥ 1, every coefficient of z.
- Proved (formalized): the continuant representation of the bounded Narayana and q = −1 series for every height,
  and the endpoint formulas for heights 4m and 4m + 1.
- Computed: for heights 4m + 2 and 4m + 3 the identity first fails at z^{h+1}; a combinatorial explanation of this
  failure is part of the referee-approved paper proof but is not formalized.
- Open: whether a corrected product formula holds at heights 4m + 2 and 4m + 3.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, web and GitHub searches and the repository checks recorded
above.
