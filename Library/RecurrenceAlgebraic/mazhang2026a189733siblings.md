---
bibkey: mazhang2026a189733siblings
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011"
doi: 10.5281/zenodo.23957584
url: https://zenodo.org/records/23957584
claim: "Corollary 2: the reduced numerators of b_n repeat the block (0, 1, 1, 1, 0, -1) with least period six; a_n = 2a_{n-6} - a_{n-12} for n >= 12; sum_{n>=0} a_n z^n = (1+z+z^2+2z^3+z^4+6z^5-z^6+2z^7+z^8+z^9-z^10)/(1-z^6)^2. Corollary 5: with p_n = num(b_n), sum_{n>=0} p_n z^n = (z+z^2+z^3-z^5)/(1-z^6) = z(1+z^2-z^3)/((1-z)(1-z+z^2)(1+z+z^2)); p_n = (1+(-1)^floor((n-1)/3))/2 - floor((n+1)/6) + floor(n/6) for n >= 0; p_n = p_{n-1} - p_{n-2} + p_{n-3} - p_{n-4} + p_{n-5} for n >= 5."
strata_touched:
  - D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries
license: CC-BY-4.0
triage: anchor
---

# Numerators, denominator recurrence and generating functions for Curtz's array

## Verified locator

Zenodo record: https://zenodo.org/records/23957584

DOI: 10.5281/zenodo.23957584 (version 2; Zenodo publication date 2026-11-04, PDF dated
3 November 2026). Source PDF:
https://zenodo.org/api/records/23957584/files/note-v2.pdf/content (text extracted locally with
layout preserved, 33,249 characters). Corollary 2 opens Section 2; Corollary 5 opens Section 3.

## Source statement

> Corollary 2. The reduced numerators of b_n repeat the block (0, 1, 1, 1, 0, −1), with least
> period six. For n ≥ 12, a_n = 2a_{n−6} − a_{n−12}. Moreover, the ordinary generating function
> of the denominator sequence is
> ∑_{n≥0} a_n z^n = (1 + z + z² + 2z³ + z⁴ + 6z⁵ − z⁶ + 2z⁷ + z⁸ + z⁹ − z¹⁰)/(1 − z⁶)².

> Proof. The numerator statement follows from (2); the value −1 occurs exactly at indices
> congruent to 5 modulo 6, so every positive period is a multiple of six. Each of the six
> subsequences in (3) is affine in k, which proves (7) for its stated range. …

> Corollary 5. For all n ≥ 0,
> ∑_{n≥0} p_n z^n = (z + z² + z³ − z⁵)/(1 − z⁶) = z(1 + z² − z³)/((1 − z)(1 − z + z²)(1 + z + z²)),
> p_n = (1 + (−1)^{⌊(n−1)/3⌋})/2 − ⌊(n+1)/6⌋ + ⌊n/6⌋.
> For n ≥ 5, p_n = p_{n−1} − p_{n−2} + p_{n−3} − p_{n−4} + p_{n−5}.
> These are A278718's generating function and Hurt's formulas dated October 3, 2017.

> Proof. Sum the period block from Corollary 2 to obtain the first fraction in (11); cancel 1 + z
> to obtain the second. Its denominator is 1 − z + z² − z³ + z⁴ − z⁵, and its numerator has
> degree four, which proves (13) for n ≥ 5. In (12), write n = 6k + r, 0 ≤ r < 6. …

## Mathematical scope

b_n = B(0,n) is the zeroth row of Curtz's rational array (see `curtz2011a189733`); a_n is the
reduced positive denominator with den(0) = 1 and p_n the reduced numerator. Both corollaries
follow from the six residue values (2) and (3) of Theorem 1, which the repository already
freezes in D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture. The floor
⌊(n−1)/3⌋ is the integer floor, equal to −1 at n = 0. Barker's generating function for a_n was
recorded as empirical in A189733 on November 11, 2016; the paper credits B. Gao's earlier proof of
the denominator recurrence and series.
