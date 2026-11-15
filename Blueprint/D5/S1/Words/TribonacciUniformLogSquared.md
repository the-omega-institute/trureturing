# A Uniform Squared Logarithm for Tribonacci Intervals

## Abstract

Every locally alternating interval charge of the literal Tribonacci word has a uniform squared-logarithmic bound.

Use the literal A-starting word W for sigma(A)=AB, sigma(B)=AC and sigma(C)=A. The letters A,B,C are 0,1,2 in Fin 3, with integer weights 2,1,0. The function signedWordSum starts positively at the beginning of the factor, even when its starting position is odd. All starts and lengths are natural numbers.

**Theorem 1.1 (One constant for every interval).**

$$\exists C \in \mathbb{R},\; 0 < C \land \left(\forall s \in \mathbb{N},\; \forall m \in \mathbb{N},\; abs\left(real\left(signedWordSum\left(factor\left(W, s, m\right)\right)\right)\right) \le C \cdot log\left(real\left(m\right) + 2\right)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TribonacciUniformLogSquared.uniform_log_squared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a strictly positive real C such that for every start s and every length m, the absolute real coercion of signedWordSum(factor W s m) is at most C times the square of the natural real logarithm of m+2. The constant is independent of s. The empty interval m=0 is included. One explicit sufficient value is C=1404/(log 2)^2.

Put tau=sigma^4. Its three literal images have lengths 13,11,7. The original formulas in TribonacciPrefixRefutation.abc_closed give complete level-j charges 2, 2-(-1)^j and 2-(2j+2)(-1)^j, each bounded by H(j)=2j+4. SubstitutionPrefixEnvelope.prefix_envelope with M=2 and B=13 therefore gives P(j)=2+13j^2+39j. Its two-block interval estimate is at most 4P(j)<=156(j+1)^2.

Every level-j image has length at least 7^j, by induction on the actual substitution. For m>0 take j=Nat.log(7,m)+1, so m<7^j. A sufficiently high actual A-iterate contains the slice starting at s of length m. MBonacciFactorWindow.factor_eq_take_drop at order 3 identifies this slice exactly with factor W s m. The identity image_add rewrites the higher iterate as a concatenation of level-j images. GoldenUniformRecurrence.flatMap_window_infix_one_or_two places the entire slice in one such image or two adjacent images. This proves the level bound independently of s.

Write k=j-1. Since 2^k<=7^k<=m, logarithmic monotonicity gives k log 2<=log(m+2). Also log 2<=log(m+2), so (j+1) log 2<=3 log(m+2). Squaring this nonnegative inequality and inserting the level estimate proves the stated constant. This is an upper bound for the exact literal word, without an assumed factor occurrence. Together with the existing prefix refutation it distinguishes a valid squared-logarithmic upper estimate from the failed logarithmic estimate. It makes no optimal-rate, spectral-gap, entropy or physical-realization assertion.

## References

- Truth anchor: `D5/S1/Words/TribonacciUniformLogSquared.uniform_log_squared`
- Dependency: [D5/S1/Words/MBonacciFactorWindow](MBonacciFactorWindow.md)
- Dependency: [D5/S1/Words/SubstitutionPrefixEnvelope](SubstitutionPrefixEnvelope.md)
- Dependency: [D5/S1/Words/TribonacciPrefixRefutation](TribonacciPrefixRefutation.md)
