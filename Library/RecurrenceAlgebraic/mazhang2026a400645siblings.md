---
bibkey: mazhang2026a400645siblings
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings"
doi: 10.5281/zenodo.24369110
url: https://zenodo.org/records/24369110
claim: "Corollary 7: with u_0 = u_1 = u_2 = 0, u_3 = 1 and u_n = u_{n-1} + u_{n-2} + u_{n-3} - u_{n-4}, the unique extension of u_n to all integer indices satisfies u_n = -u_{2-n}, the identity recorded by Michael Somos (July 25, 2025) in A116732, revision 33, FORMULA."
strata_touched:
  - D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal
license: CC-BY-4.0
triage: anchor
---

# Bilateral reversal of the unrounded A116732 companion

## Verified locator

Zenodo record: https://zenodo.org/records/24369110

DOI: 10.5281/zenodo.24369110 (version 2; Zenodo publication date 2026-11-19, PDF dated
9 November 2026). Concept DOI 10.5281/zenodo.24369109 is distinct. Source PDF:
https://zenodo.org/api/records/24369110/files/note-v2.pdf/content (text extracted locally with
pdftotext -layout, 25,795 characters). Corollary 7 is in Section 5.

## Source statement

> The unrounded companion in A116732 [3] has u0 = u1 = u2 = 0, u3 = 1, and
> un = un−1 + un−2 + un−3 − un−4 for n ≥ 4.

> Corollary 7. The unique extension of un to all integer indices satisfies un = −u2−n, the
> identity recorded by Michael Somos (July 25, 2025) in A116732, revision 33, FORMULA.

> Proof. The recurrence has invertible last coefficient, so determines the extension uniquely,
> with u−1 = −1. Its palindromic characteristic polynomial makes −u2−n another solution; its
> values at n = 0, 1, 2, 3 are 0, 0, 0, 1. Uniqueness proves the identity.

## Mathematical scope

The integer-indexed extension is the unique function u : ℤ → ℤ with the four initial values
that satisfies the recurrence at every integer n; the trailing coefficient −1 is a unit, so the
recurrence runs backwards. The identity concerns this unrounded companion, not the rounded
squares of A400645 (see `oeis2026a400645`). The reversal identity is credited to Michael Somos
in A116732, revision 33, FORMULA; R. K. Guy's entry supplies the recurrence and generating
function z³/Q(z) with Q(z) = z⁴ − z³ − z² − z + 1.
