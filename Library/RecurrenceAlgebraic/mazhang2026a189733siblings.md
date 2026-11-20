---
bibkey: mazhang2026a189733siblings
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Curtz's denominator conjecture: OEIS A189733, revision 12, COMMENTS, May 23, 2011"
doi: 10.5281/zenodo.23957584
url: https://zenodo.org/records/23957584
claim: "Corollary 2: the reduced numerators of b_n repeat the block (0, 1, 1, 1, 0, -1) with least period six; a_n = 2a_{n-6} - a_{n-12} for n >= 12; sum_{n>=0} a_n z^n = (1+z+z^2+2z^3+z^4+6z^5-z^6+2z^7+z^8+z^9-z^10)/(1-z^6)^2. Corollary 3: for every n >= 0, B(n,0) = sum_{j=0}^{n} (-1)^{n-j} C(n,j) b_j = (-1)^{n+1} b_n; its proof shows the reflection B(m,n) = (-1)^{m+n+1} B(n,m) and the difference identity B(m+1,n) = B(m,n+1) - B(m,n) for all m, n >= 0. Corollary 4: for m >= 0 and d >= 1, B(m,m+d) = (-1)^m sum_{j=0}^{floor((d-1)/2)} (-1)^j C(d-1-j, j)/(m+j+1); together with B(m,m) = 0 and B(m,n) = (-1)^{m+n+1} B(n,m), this determines the whole square array. Corollary 5: with p_n = num(b_n), sum_{n>=0} p_n z^n = (z+z^2+z^3-z^5)/(1-z^6) = z(1+z^2-z^3)/((1-z)(1-z+z^2)(1+z+z^2)); p_n = (1+(-1)^floor((n-1)/3))/2 - floor((n+1)/6) + floor(n/6) for n >= 0; p_n = p_{n-1} - p_{n-2} + p_{n-3} - p_{n-4} + p_{n-5} for n >= 5. Corollary 6: with c_n = (n+1)/a_n, (c_{6k}, ..., c_{6k+5}) = (6k+1, 2, 3, 2, 6k+5, 1) for every k >= 0; c_n = 2c_{n-6} - c_{n-12} for n >= 12; sum_{n>=0} c_n z^n = (1+2z+3z^2+2z^3+5z^4+z^5+5z^6-2z^7-3z^8-2z^9+z^10-z^11)/(1-z^6)^2; and c_{2n+1} = A130196(n+1), c_{A047245(n+1)} = A052901(n+2), c_{3n} + c_{3n+1} + c_{3n+2} = A047238(n+3) for n >= 0. Corollary 7: with C(m,n) = 2B(m,n+1) - B(m,n), d_m = den(C(m,m+3)) and g_m = gcd(3,m+2), for every m >= 0, C(m,m+3) = (-1)^{m+1}(2m+1)/((m+1)(m+2)) and d_m = (m+1)(m+2)/g_m; (d_{3k}, d_{3k+1}, d_{3k+2}) = ((3k+1)(3k+2), (k+1)(3k+2), 3(k+1)(3k+4)) for k >= 0; sum_{m>=0} d_m z^m = 2(1+z+6z^2+7z^3+2z^4+3z^5+z^6)/(1-z^3)^3; d_m = (m+1)A051176(m+2) and d_{m+2} = 2A306368(m) for m >= 0; C(m,m+3) = (-1)^{m+1}A146535(m+1)/d_m, not (-1)^{m+1}A146535(m)/d_m. Corollary 8: sum_{m>=0} 1/d_m = 1 + log 3 - pi/(3 sqrt 3). Corollary 9: for the unsigned array U with zero diagonal, U(m,m+1) = 1/(m+1) and the same recurrence, u_n = U(0,n) = (L_{n+1} - 1)/(n+1) for n >= 0 with Lucas numbers L_0 = 2, L_1 = 1; for r >= 0 the reduced numerator and denominator of u_{2r+1} are A175385(r+1) and A175386(r+1), so A242926's formula with A175386(r) requires this shift; sum_{j=0}^{n} (-1)^{n-j} C(n,j) u_j = (-1)^{n+1} u_n; and sum_{m=0}^{r} U(m, 2r+1-m) = u_{2r+2} for r >= 0."
strata_touched:
  - D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries
  - D5/S1/Recurrence/Residue/OEISA267068Quotients
  - D5/S1/Recurrence/Residue/OEISA189733FiniteSums
  - D5/S1/Recurrence/Residue/OEISA189733Reflection
  - D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal
  - D5/S1/Recurrence/Residue/OEISA194767ReciprocalSum
  - D5/S1/Recurrence/Residue/OEISA242926UnsignedLucasRow
license: CC-BY-4.0
triage: anchor
---

# Numerators, denominator recurrence and generating functions for Curtz's array

## Verified locator

Zenodo record: https://zenodo.org/records/23957584

DOI: 10.5281/zenodo.23957584 (version 2; Zenodo publication date 2026-11-04, PDF dated
3 November 2026). Source PDF:
https://zenodo.org/api/records/23957584/files/note-v2.pdf/content (text extracted locally with
layout preserved, 33,249 characters). Corollaries 2, 3 and 4 are in Section 2; Corollaries 5 and 6 are in Section 3;
Corollaries 7 and 8 are in Section 4;
Corollary 9 is in Section 5.

## Source statement

> Corollary 2. The reduced numerators of b_n repeat the block (0, 1, 1, 1, 0, −1), with least
> period six. For n ≥ 12, a_n = 2a_{n−6} − a_{n−12}. Moreover, the ordinary generating function
> of the denominator sequence is
> ∑_{n≥0} a_n z^n = (1 + z + z² + 2z³ + z⁴ + 6z⁵ − z⁶ + 2z⁷ + z⁸ + z⁹ − z¹⁰)/(1 − z⁶)².

> Proof. The numerator statement follows from (2); the value −1 occurs exactly at indices
> congruent to 5 modulo 6, so every positive period is a multiple of six. Each of the six
> subsequences in (3) is affine in k, which proves (7) for its stated range. …

> Corollary 3. For every n ≥ 0, B(n, 0) = ∑_{j=0}^{n} (−1)^{n−j} C(n, j) bj = (−1)^{n+1} bn.

> Proof. First, B(m, n) = (−1)^{m+n+1} B(n, m). To prove this when m > n, define the lower entries
> by the expression on the right, retaining the upper triangle. … The difference identity
> B(m + 1, n) = B(m, n + 1) − B(m, n) holds for all m, n ≥ 0. … Iterating this difference identity,
> or using induction and Pascal's identity, gives B(m, n) = ∑_{j=0}^{m} (−1)^{m−j} C(m, j)
> B(0, n + j). Set n = 0 and use reflection to obtain (9).

> Corollary 4. For m ≥ 0 and d ≥ 1,
> B(m, m + d) = (−1)^m ∑_{j=0}^{⌊(d−1)/2⌋} (−1)^j C(d−1−j, j)/(m + j + 1).
> Together with B(m, m) = 0 and B(m, n) = (−1)^{m+n+1} B(n, m), this determines the whole square
> array.

> Proof. Pascal's identity shows that Qd(t) = ∑_{j=0}^{⌊(d−1)/2⌋} (−1)^j C(d−1−j, j) t^j has
> initial values Q1 = Q2 = 1 and satisfies Qd+2 = Qd+1 − tQd. Substitution in (4) gives (10);
> reflection was proved in Corollary 3. The case m = 0 is Gao's finite-sum formula [2].

> Corollary 5. For all n ≥ 0,
> ∑_{n≥0} p_n z^n = (z + z² + z³ − z⁵)/(1 − z⁶) = z(1 + z² − z³)/((1 − z)(1 − z + z²)(1 + z + z²)),
> p_n = (1 + (−1)^{⌊(n−1)/3⌋})/2 − ⌊(n+1)/6⌋ + ⌊n/6⌋.
> For n ≥ 5, p_n = p_{n−1} − p_{n−2} + p_{n−3} − p_{n−4} + p_{n−5}.
> These are A278718's generating function and Hurt's formulas dated October 3, 2017.

> Proof. Sum the period block from Corollary 2 to obtain the first fraction in (11); cancel 1 + z
> to obtain the second. Its denominator is 1 − z + z² − z³ + z⁴ − z⁵, and its numerator has
> degree four, which proves (13) for n ≥ 5. In (12), write n = 6k + r, 0 ≤ r < 6. …

> Corollary 6. For every k ≥ 0, (c6k, . . . , c6k+5) = (6k + 1, 2, 3, 2, 6k + 5, 1).
> In particular, cn = 2cn−6 − cn−12 for n ≥ 12, and
> ∑_{n≥0} cn z^n = (1 + 2z + 3z² + 2z³ + 5z⁴ + z⁵ + 5z⁶ − 2z⁷ − 3z⁸ − 2z⁹ + z¹⁰ − z¹¹)/(1 − z⁶)².
> Thus both conjectures attributed to Barker on January 10, 2016, in A267068 are true. Its other
> three FORMULA assertions hold, with the OEIS offsets of the cited sequences [5]:
> c2n+1 = A130196(n + 1), cA047245(n+1) = A052901(n + 2),
> c3n + c3n+1 + c3n+2 = A047238(n + 3) (n ≥ 0).

> Proof. Equation (14) follows by dividing n + 1 by (3). Its six affine subsequences have
> intercepts (1, 2, 3, 2, 5, 1) and slopes (6, 0, 0, 0, 6, 0). …

> For the full difference array put C(m, n) = 2B(m, n + 1) − B(m, n). …
> Corollary 7. Let d_m = den(C(m, m + 3)) and g_m = gcd(3, m + 2). For every m ≥ 0,
> C(m, m + 3) = (−1)^{m+1}(2m + 1)/((m + 1)(m + 2)), d_m = (m + 1)(m + 2)/g_m.
> Consequently, for k ≥ 0,
> (d_{3k}, d_{3k+1}, d_{3k+2}) = ((3k + 1)(3k + 2), (k + 1)(3k + 2), 3(k + 1)(3k + 4)),
> ∑_{m≥0} d_m z^m = 2(1 + z + 6z² + 7z³ + 2z⁴ + 3z⁵ + z⁶)/(1 − z³)³.
> The two shifted-sequence formulas in A194767 also hold:
> d_m = (m + 1)A051176(m + 2), d_{m+2} = 2A306368(m) (m ≥ 0).
> Its fourth-diagonal numerator formula requires a shift:
> C(m, m + 3) = (−1)^{m+1}A146535(m + 1)/d_m, not (−1)^{m+1}A146535(m)/d_m.

> Proof. … Since gcd(2m + 1, m + 1) = 1 and gcd(2m + 1, m + 2) = gcd(3, m + 2), reduction gives
> d_m. … The cited definitions [8] are A051176(r) = r/gcd(r, 3) and A306368(r) equal to the
> reduced numerator of (r + 3)(r + 4)/((r + 1)(r + 2)). … A146535(r), indexed from r = 1, is the
> reduced numerator of (2r − 1)/3. Thus A146535(m + 1) = (2m + 1)/g_m, proving (20). The
> unshifted formula is already false at m = 2: its unsigned numerator is A146535(2) = 1, whereas
> C(2, 5) = −5/12.

> Corollary 8. The reciprocal sum stated in A194767 is ∑_{m≥0} 1/d_m = 1 + log 3 − π/(3√3).

> Proof. Because g_m = 1 + 2·1_{m≡1 (mod 3)}, telescoping gives
> ∑_{m≥0} 1/d_m = 1 + 2 ∑_{k≥0} (1/(3k + 2) − 1/(3k + 3)) = 1 + 2 ∫_0^1 x/(1 + x + x²) dx
> = 1 + log 3 − π/(3√3). The summands represented by x^{3k+1}(1 − x) are nonnegative, justifying
> termwise integration. An antiderivative is ½ log(x² + x + 1) − (1/√3) arctan((2x + 1)/√3).

> The related entries A189731 and A242926 [9] use the same array recurrence with the unsigned
> boundary U(m, m + 1) = 1/(m + 1) and zero diagonal. Write u_n = U(0, n) and let L_0 = 2, L_1 = 1,
> L_{n+2} = L_{n+1} + L_n be the Lucas numbers.
> Corollary 9. For n ≥ 0, u_n = (L_{n+1} − 1)/(n + 1). For r ≥ 0, the odd-index reduced numerator
> is A175385(r + 1) and the reduced denominator is A175386(r + 1) [10]. In particular, A242926's
> formula with A175386(r) requires this shift. The inverse-binomial identity is
> ∑_{j=0}^{n} (−1)^{n−j} C(n, j) u_j = (−1)^{n+1} u_n.
> The upper antidiagonal assertion in A242926 is ∑_{m=0}^{r} U(m, 2r + 1 − m) = u_{2r+2} (r ≥ 0).

> Proof. … The same unsigned moment argument gives
> u_{2r+1} = ∑_{j=0}^{r} C(2r − j, j)/(j + 1) = ∑_{i=1}^{r+1} C(2(r + 1) − i − 1, i − 1)/i,
> which is the defining fraction for A175385 and A175386 at r + 1. At r = 1, A242926(3) = 2 but
> A175386(1) = 1, verifying the unshifted identity's failure. The reflection and difference proof
> of Corollary 3 applies unchanged to any first-superdiagonal seed, yielding the inverse-binomial
> identity. Finally, iterating the upper recurrence along the antidiagonal telescopes u_{2r+2} into
> the displayed sum; its last remainder is U(r + 1, r + 1) = 0.

## Mathematical scope

b_n = B(0,n) is the zeroth row of Curtz's rational array (see `curtz2011a189733`); a_n is the
reduced positive denominator with den(0) = 1 and p_n the reduced numerator. Both corollaries
follow from the six residue values (2) and (3) of Theorem 1, which the repository already
freezes in D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture. The floor
⌊(n−1)/3⌋ is the integer floor, equal to −1 at n = 0. Barker's generating function for a_n was
recorded as empirical in A189733 on November 11, 2016; the paper credits B. Gao's earlier proof of
the denominator recurrence and series.

For Corollary 6, c_n = (n + 1)/a_n is A267068, revision 11, whose FORMULA field records the
recurrence and generating function as conjectures from Colin Barker (January 10, 2016). The
cited sequences are taken with their OEIS offsets: A130196 (period 3, repeat [1, 2, 2], offset 0),
A047245 (numbers congruent to 1, 2 or 3 mod 6, offset 1), A052901 (period 3 with a(3n) = 3 and
a(3n+1) = a(3n+2) = 2, offset 0) and A047238 (numbers congruent to 0 or 2 mod 6, offset 1).

The full square array B uses the upper branch B(m, m) = 0, B(m, m + 1) = (−1)^m/(m + 1),
B(m, n) = B(m, n − 1) + B(m + 1, n − 1) for n ≥ m + 2, and the lower branch
B(m, n) = B(m − 1, n + 1) − B(m − 1, n) for m > n, as in the A189733 Maple and Mathematica
programs.

For Corollary 7, C(m, n) = 2B(m, n + 1) − B(m, n) is the second-kind companion array of A194767,
so its fourth diagonal C(m, m + 3) is 2B(m, m + 4) − B(m, m + 3), written in terms of the frozen
upper-triangle entries. The cited sequences follow the paper's definitions: A051176(r) =
r/gcd(r, 3) from offset 0, A306368(r) the reduced numerator of (r + 3)(r + 4)/((r + 1)(r + 2))
from offset 0, and A146535(r) the reduced numerator of (2r − 1)/3 from offset 1.

For Corollary 9, the unsigned array U has the same zero diagonal, upper recurrence and lower
branch as B, with seed U(m, m + 1) = 1/(m + 1). The Lucas numbers are the repository's
`goldenLucas`, the trace of the golden powers, with L_0 = 2 and L_1 = 1. A175385 and A175386 are
the reduced numerator and denominator of ∑_{i=1}^{n} C(2n − i − 1, i − 1)/i, from offset 1;
A242926(n) is the reduced denominator of u_n from offset 0.
