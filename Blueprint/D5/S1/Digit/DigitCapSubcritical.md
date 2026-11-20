# A uniform subcritical bound for digit caps

## Abstract

Digit caps at most ell^r−2 allow at most Q^(m mod 2) H^⌊m/2⌋ representations below ell^(m+1), with Q = ell^(r−1) and H = Q²−Q/ell, so the growth exponent stays below r−1.

**Theorem 1.1 (The subcritical bound).**

Lean statement: `D5/S1/Digit/DigitCapSubcritical.subcritical`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapSubcritical.subcritical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Coons (2026). *The Calkin–Wilf problems on ℓ-ary partition functions, arXiv:2611.08109v1*. URL: <https://arxiv.org/html/2611.08109v1>.

*Commentary.*

For ell ≥ 2, r ≥ 2 and a cap k ≤ ell^r−2, every n < ell^(m+1) has at most Q^(m mod 2) H^⌊m/2⌋ representations with digits at most k, where Q = ell^(r−1) and H = Q²−Q/ell. The lowest digit of a representation of n lies in the residue class of n; up to the cap a class has at most Q members and the class ell−1 at most Q−1. As the lowest digit runs through its class, the class of the next digit runs through every residue Q/ell times, so two consecutive digits have at most Q²−Q/ell joint choices, and the bound follows by induction two digits at a time. Hence b(k,ell,n) = O(n^((log_ell H)/2)) and (log_ell H)/2 < r−1, because H < Q² = ell^(2(r−1)). It improves the quotient bound Q^m when the cap is at most ell^r−2. M. Coons lists CW2 (is ell²−1 the first cap with linear maximal growth?) in Section 1 and notes in Section 3 that sublinear maximal growth of b(ell²−2, ell, n) would suffice; the case r = 2 gives it. The all-r bound is Theorem 1 of the outreach note registered with the request.

## References

- Truth anchor: `D5/S1/Digit/DigitCapSubcritical.subcritical`
- Dependency: [D5/S1/Digit/DigitCapQuotientBound](DigitCapQuotientBound.md)
