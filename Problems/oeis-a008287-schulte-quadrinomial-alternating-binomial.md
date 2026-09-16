---
slug: oeis-a008287-schulte-quadrinomial-alternating-binomial
bibkey: schulte2015a008287
doi: null
url: https://oeis.org/A008287
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion
---

# Schulte's A008287 alternating-binomial expansion

## Problem

OEIS A008287, NAME (`%N`, verbatim):

> Triangle of quadrinomial coefficients, row n is the sequence of coefficients of (1 + x + x^2 + x^3)^n.

The settled FORMULA (`%F`, verbatim) is:

> T(n,k) = Sum_{j=0..k} (-2)^j*binomial(n,j)*binomial(3*n-2*j,k-j) for n >= 0 and 0 <= k <= 3*n (conjectured). - _Werner Schulte_, Sep 09 2015

The full-quantifier reading is: for all `n k : ℕ`, if `k ≤ 3 * n`,
the integer coefficient `T n k` of `X^k` in
`(1 + X + X^2 + X^3 : ℤ[X]) ^ n` equals
`∑ j ∈ Finset.range (k + 1), (-2 : ℤ)^j * (n.choose j : ℤ) *
((3 * n - 2 * j).choose (k - j) : ℤ)`. Subtraction in binomial indices
is truncated natural subtraction, and `n.choose j = 0` for `j > n`.
The scope wall is only this Schulte 2015 formula. The Shevelev 2010 and
Bala 2013 formulas in the same entry are different and are not settled here.

## Motivation

The independent question is Schulte's named expansion of all A008287
quadrinomial coefficients at indices `0 ≤ k ≤ 3n`. The public surface
contains only the A008287 coefficient definition `T` and its formula `result`.

## Gap

Readings of 2026-09-16: the OEIS entry still marks the formula `(conjectured)`
(added 2015-09-09) with no proof line; OpenAlex
`quadrinomial coefficients binomial identity` returned 8 hits, none about this
expansion; Math.SE API returned 0 hits; GitHub code search in
`google-deepmind/formal-conjectures` returned 0 hits; the arXiv API gave no
response; the entry's linked Fahssi 2012 (arXiv:1202.0228) predates the
conjecture and was not checked page by page (ASSUMED-UNVERIFIED). The named
expansion was not found on those searched surfaces.

Repository prior art at `origin/dev`: `git grep -i -E 'A008287|quadrinomial'
origin/dev -- D5 Blueprint Library Problems` returned 0 hits.
`coeff_one_add_X_pow` is used by 5 D5 modules, none stating this expansion.
Pinned Mathlib supplies `add_pow`, `Polynomial.coeff_one_add_X_pow`,
`Polynomial.coeff_X_pow_mul'`, and `Polynomial.finsetSum_coeff`; a
case-insensitive search for `A008287|quadrinomial|schulte` in pinned Mathlib
returned 0 hits.
Numerics for `0 ≤ n ≤ 30` and every `0 ≤ k ≤ 3n` cover 1426 pairs with
zero exceptions; finite checks do not prove the universally quantified line.

Pre-registration: issue #8204 (2026-09-15T21:41:20Z).

The theorem has proof shape `bind-only` and admission basis
`open-problem-resolution` under pre-registration issue #8204: it instantiates
and normalizes pinned Mathlib lemmas to settle the previously named formula.
There is no escape witness, no helper theorem declaration, and no direct
frozen D5 dependency (Mathlib only).

## Route

1. Factor `1+X+X²+X³` as `(1+X)³−2X(1+X)` in `ℤ[X]`.
2. Apply `add_pow` and regroup powers, with `3(n−j)+j = 3n−2j` for `j≤n`.
3. Extract the degree-`k` coefficient using the `X^j` shift and the
   binomial coefficients of `(1+X)^(3n−2j)`.
4. Reindex the resulting finite sum over `j≤min(n,k)` to `j=0..k`:
   terms with `j>n` vanish through `binom(n,j)=0`.

## Falsifier

Any natural pair `n,k` with `k≤3n` at which the extracted coefficient
differs from the displayed alternating-binomial sum would refute the claim.

## Evidence

- Final Lean module: `D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.lean`;
  116 lines and 4920 UTF-8 bytes (`wc -lc`, exit 0); its directory has 38
  Lean files.
- `lake env lean D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.lean`:
  exit 0, zero warnings.
- `tools/scripts/agent/header-check.sh
  D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.lean`:
  exit 0.
- Final-source scratch `#print axioms T` and `#print axioms result`:
  exit 0; each reports `[propext, Classical.choice, Quot.sound]`.
- The module's sole direct import is `Mathlib.Algebra.Polynomial.Coeff`;
  deleting it makes `lake env lean` exit 1 (unknown `Polynomial`), so it is
  load-bearing.
- Exact-integer check of the final coefficient definition for every
  `0 ≤ n ≤ 30` and `0 ≤ k ≤ 3n`: exit 0; 1426 pairs, zero exceptions.

## Triage

`theorem`; resolution `proved` for the stated Schulte 2015 formula.
The Scribe theorem node carries the corresponding
`OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

## ASSUMED-UNVERIFIED

Historical openness beyond the listed OEIS, OpenAlex, Math.SE, and GitHub
surfaces is unverified. The arXiv API gave no response; Fahssi 2012 was not
checked page by page. No exhaustive novelty or priority claim is made.
