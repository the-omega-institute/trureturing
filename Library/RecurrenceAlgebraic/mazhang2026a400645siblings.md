---
bibkey: mazhang2026a400645siblings
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings"
doi: 10.5281/zenodo.24369110
url: https://zenodo.org/records/24369110
claim: "Corollary 6: for the A400645 source sequence a_n and every fixed integer h >= 0, a_{n+h}/a_n -> lambda^h, and log(a_n)/n -> log lambda. Corollary 7: with u_0 = u_1 = u_2 = 0, u_3 = 1 and u_n = u_{n-1} + u_{n-2} + u_{n-3} - u_{n-4}, the unique extension of u_n to all integer indices satisfies u_n = -u_{2-n}, the identity recorded by Michael Somos (July 25, 2025) in A116732, revision 33, FORMULA. Corollary 8: the coefficients v_n of (1+z)^2(1-z+z^2-z^3+z^4-z^5+z^6)/((1-z+z^2)Q(z)), Q(z) = z^4-z^3-z^2-z+1, are strictly increasing for n >= 0, proving the conjecture in Kimberling's A289916, revision 11, COMMENTS; moreover v_n = D r^n + O(1) for some D > 0."
strata_touched:
  - D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal
  - D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease
  - D5/S1/Recurrence/OEISA400645FixedLagGrowth
license: CC-BY-4.0
triage: anchor
---

# Algebraic companions of the A400645 recurrence

## Verified locator

Zenodo record: https://zenodo.org/records/24369110

DOI: 10.5281/zenodo.24369110 (version 2; Zenodo publication date 2026-11-19, PDF dated
9 November 2026). Concept DOI 10.5281/zenodo.24369109 is distinct. Source PDF:
https://zenodo.org/api/records/24369110/files/note-v2.pdf/content (text extracted locally with
pdftotext -layout, 25,795 characters). Corollaries 6, 7 and 8 are in Section 5.

## Source statement

> Corollary 6. For every fixed integer h ≥ 0, an+h/an → λh, and log(an)/n → log λ.

> Proof. Both statements follow directly from an ∼ cλn with c > 0; the logarithm is defined for
> n ≥ 4.

> The unrounded companion in A116732 [3] has u0 = u1 = u2 = 0, u3 = 1, and
> un = un−1 + un−2 + un−3 − un−4 for n ≥ 4.

> Corollary 7. The unique extension of un to all integer indices satisfies un = −u2−n, the
> identity recorded by Michael Somos (July 25, 2025) in A116732, revision 33, FORMULA.

> Proof. The recurrence has invertible last coefficient, so determines the extension uniquely,
> with u−1 = −1. Its palindromic characteristic polynomial makes −u2−n another solution; its
> values at n = 0, 1, 2, 3 are 0, 0, 0, 1. Uniqueness proves the identity.

> Corollary 8. The increasing-sequence conjecture in Kimberling's A289916, revision 11,
> COMMENTS, holds: its coefficients vn are strictly increasing for n ≥ 0. Moreover
> vn = Drn + O(1) for some D > 0, so their consecutive-ratio limit is the number defined in
> A289917 [6].

> Proof. Colin Barker's July 19, 2017 formula in A289916 gives
> F(z) = ∑ vn zn = (1 + z)2(1 − z + z2 − z3 + z4 − z5 + z6)/((1 − z + z2)Q(z))
> = (1 + z)2(1 + z7)/((1 + z3)Q(z)). … Now let H(z) = 1/((1 + z3)Q(z)) = ∑ hn zn, with hn = 0
> for n < 0. Since (1 + z3)Q(z) = 1 − z − z2 − z5 − z6 + z7, one has h0 = 1 and, for n ≥ 1,
> hn − hn−1 = hn−2 + hn−5 + hn−6 − hn−7. Induction shows that hn is nondecreasing, and strictly
> increasing for n ≥ 2: the right side is nonnegative and contains hn−2 ≥ 1 then.
> Multiplication by (1 + z)2(1 + z7) preserves nonnegative differences; for n = 1, v1 − v0 = 2,
> and for n ≥ 2 the hn summand gives strictness.

## Mathematical scope

The integer-indexed extension is the unique function u : ℤ → ℤ with the four initial values
that satisfies the recurrence at every integer n; the trailing coefficient −1 is a unit, so the
recurrence runs backwards. The identity concerns this unrounded companion, not the rounded
squares of A400645 (see `oeis2026a400645`). The reversal identity is credited to Michael Somos
in A116732, revision 33, FORMULA; R. K. Guy's entry supplies the recurrence and generating
function z³/Q(z) with Q(z) = z⁴ − z³ − z² − z + 1.

For Corollary 8, Q is the same quartic, and the conjecture's exact wording in A289916, revision
11, COMMENTS, is "Conjecture: the sequence is strictly increasing." The generating function is
credited to Colin Barker (July 19, 2017) in A289916, FORMULA.

For Corollary 6, a_n is the A400645 source sequence and λ = √r its limiting ratio, as in the
frozen module `D5/S1/Recurrence/OEISA400645` (see `oeis2026a400645`).
