# The least digit caps for polynomial and linear growth

## Abstract

The least digit cap whose upper growth exponent reaches r−1 is ell^r−1, and the least cap whose counts grow at least linearly is ell²−1.

**Theorem 1.1 (The least cap with upper exponent r−1).**

Lean statement: `D5/S1/Digit/DigitCapLeastCap.least_cap`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapLeastCap.least_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Coons (2026). *The Calkin–Wilf problems on ℓ-ary partition functions, arXiv:2611.08109v1*. URL: <https://arxiv.org/html/2611.08109v1>.

*Commentary.*

For ell ≥ 2 and r ≥ 2, ell^r−1 is the least cap k whose upper exponent limsup log b(k,ell,n)/log n is at least r−1. The cap ell^r−1 has at least n^(r−1)/C representations for large n by the Θ(n^(r−1)) bound, so along every tail log b/log n comes arbitrarily close to r−1 from below. Every cap k ≤ ell^r−2 has b(k,ell,n) = O(n^e) with e = (log_ell H)/2 < r−1, so its upper exponent is at most a value strictly between e and r−1. With the exact count n/ell+1 at the cap ell²−1, the case r = 2 answers CW2 of M. Coons, which he lists as open, in the sense that no smaller cap has upper exponent at least 1. The statement is Corollary 2 of the outreach note registered with the request.

**Theorem 1.2 (The least cap with linear minimal growth).**

Lean statement: `D5/S1/Digit/DigitCapLeastCap.least_linear_min`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapLeastCap.least_linear_min` (`✓ std3`). ∎

*Citation.* Michael Coons (2026). *The Calkin–Wilf problems on ℓ-ary partition functions, arXiv:2611.08109v1*. URL: <https://arxiv.org/html/2611.08109v1>.

*Commentary.*

For ell ≥ 2, ell²−1 is the least cap k with c·n ≤ b(k,ell,n) for some c > 0 and all large n. At ell²−1 the count is exactly ⌊n/ell⌋+1. For a smaller cap the count is O(n^e) with e < 1, and c·n ≤ C·n^e fails once (1−e)·log n exceeds |log C|+|log c|. This is CW3 of M. Coons, answered by his Theorem 1.

## References

- Truth anchor: `D5/S1/Digit/DigitCapLeastCap.least_cap`
- Truth anchor: `D5/S1/Digit/DigitCapLeastCap.least_linear_min`
- Dependency: [D5/S1/Digit/DigitCapPowerGF](DigitCapPowerGF.md)
- Dependency: [D5/S1/Digit/DigitCapSubcritical](DigitCapSubcritical.md)
