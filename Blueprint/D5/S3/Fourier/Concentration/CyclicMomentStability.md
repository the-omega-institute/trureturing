# Stability from Two Fourier Moments

## Abstract

A real projection variance controls two phase errors from a common probability weight.

Take a finite indexed family of complex unit phases z(j) with nonnegative real weights w(j) of total mass one. Let m be the weighted first moment, b the weighted second moment, and c the squared magnitude of m. Set X(j) to the conjugate of m times z(j). Suppose c lies strictly between zero and one. Let t be the positive square root of c(1−c). Let eta(j) equal 1 at a nonnegative imaginary part of X(j) and −1 at a negative imaginary part. Define D as c/2 minus c squared plus half the real part of the product of b and the squared conjugate of m.

**Theorem 1.1 (Phase error and mass balance).**

$$\sum_{j} \operatorname{w}\left(j\right) \cdot \left|\operatorname{X}\left(j\right)-c-i \cdot \operatorname{eta}\left(j\right) \cdot t\right|^{2} \leq (1 + \frac{4}{t^{2}}) \cdot D \land (\sum_{j} \operatorname{w}\left(j\right) \cdot \operatorname{eta}\left(j\right))^{2} \leq \frac{4 \cdot D}{t^{4}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted mean of X is c and its imaginary mean is zero. The unit-circle identity and the second moment identify D with the weighted variance of the real part of X. Write x and y for the real and imaginary parts at one index. The squared imaginary magnitudes obey y squared minus t squared equal to c squared minus x squared. Factoring and using |x+c| at most two bounds the squared imaginary error by 4/t squared times the squared real error. Summing and using the weighted Cauchy–Schwarz inequality gives the two bounds.

The interval for c gives two distinct comparison points and a positive divisor. The unit-phase condition gives the pointwise norm identity. Nonnegative weights allow the pointwise estimates to be summed, and mass one fixes the mean and the Cauchy–Schwarz factor. When b=0, D becomes c/2 minus c squared. At c=1/2 this forces both errors to vanish. The comparison points lie on the scaled unit circle. A quantitative separation estimate for a discrete cyclic grid and a bound for weighted near-collisions of actual zeta ordinates at growing order remain separate questions.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability`
