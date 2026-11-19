# The least digit cap with upper exponent r−1

## Abstract

The least digit cap whose upper growth exponent reaches r−1 is ell^r−1; for r = 2 it is the least cap with linear maximal growth.

**Theorem 1.1 (The least cap).**

Lean statement: `D5/S1/Digit/DigitCapLeastCap.least_cap`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapLeastCap.least_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Coons (2026). *The Calkin–Wilf problems on ℓ-ary partition functions, arXiv:2611.08109v1*. URL: <https://arxiv.org/html/2611.08109v1>.

*Commentary.*

For ell ≥ 2 and r ≥ 2, ell^r−1 is the least cap k whose upper exponent limsup log b(k,ell,n)/log n is at least r−1. The cap ell^r−1 has at least C(⌊n/ell^(r−1)⌋+r−1, r−1) ≥ (n/ell^(r−1))^(r−1)/(r−1)! representations, so log b/log n ≥ (r−1) + log c/log n along every tail and the upper exponent is at least r−1. Every cap k ≤ ell^r−2 has b(k,ell,n) = O(n^e) with e = (log_ell H)/2 < r−1, so its upper exponent is at most a value strictly between e and r−1. For r = 2 this answers CW2 of M. Coons positively: ell²−1 is the least cap with linear maximal growth. The statement is Corollary 2 of the outreach note registered with the request.

## References

- Truth anchor: `D5/S1/Digit/DigitCapLeastCap.least_cap`
- Dependency: [D5/S1/Digit/DigitCapPowerGF](DigitCapPowerGF.md)
- Dependency: [D5/S1/Digit/DigitCapSubcritical](DigitCapSubcritical.md)
