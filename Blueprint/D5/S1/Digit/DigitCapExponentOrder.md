# Real values, order and cap monotonicity of the growth exponents

## Abstract

The upper and lower bounded-digit growth exponents are finite nonnegative reals, the lower one is at most the upper one, and both are monotone in the cap.

**Theorem 1.1 (Finite, ordered and monotone exponents).**

Lean statement: `D5/S1/Digit/DigitCapExponentOrder.exponents_real_ordered_monotone`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapExponentOrder.exponents_real_ordered_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural ell and k with 2≤ell and ell−1≤k, there are real numbers A and L with exponent k ell=A and lowerExponent k ell=L, 0≤L and L≤A. Moreover exponent k ell≤exponent (k+1) ell and lowerExponent k ell≤lowerExponent (k+1) ell. Here exponent is the extended-real infimum over N≥2 of the supremum over n≥N, and lowerExponent the supremum over N≥2 of the infimum over n≥N, of log(count k ell n)/log n.

For n≥2 the count is at least one, so every readout is nonnegative. With m=⌊log_ell n⌋ we have n<ell^(m+1) and ell^m≤n; since k≤(k+1)·ell−1, the quotient-digit bound gives count k ell n≤(k+1)^m, so every readout is at most log(k+1)/log ell. Hence both exponents lie between 0 and this bound and are real. Any tail infimum from N is at most the readout at max(N,M), which is at most the tail supremum from M, so the lower exponent is at most the upper one. A representation with digits at most k is also one with digits at most k+1, so the count, and with it every readout from n=2 on, does not decrease when the cap grows; both tail operations preserve this inequality.

## References

- Truth anchor: `D5/S1/Digit/DigitCapExponentOrder.exponents_real_ordered_monotone`
- Dependency: [D5/S1/Digit/DigitCapLowerExponent](DigitCapLowerExponent.md)
- Dependency: [D5/S1/Digit/DigitCapQuotientBound](DigitCapQuotientBound.md)
