# Convolution in L²

## Abstract

Concrete convolution bounds for square-integrable functions.

**Theorem 1.1 (Complexification of real convolution).**

Lean statement: `D5/S3/Analytic/Fourier/ConvolutionL2.real_convolution_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ConvolutionL2.real_convolution_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Convolving the complexifications of two real functions agrees with the complexification of their real convolution integral.

**Theorem 1.2 (Young’s inequality in L²).**

Lean statement: `D5/S3/Analytic/Fourier/ConvolutionL2.convolution_memLp_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ConvolutionL2.convolution_memLp_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If q is integrable and f is square-integrable on the real line, their multiplication convolution is square-integrable and its L² norm is at most the integral of the norm of q times the L² norm of f. Weighted Cauchy–Schwarz bounds the squared integrand, and Tonelli together with translation invariance gives the norm estimate.

**Theorem 1.3 (Bounded Schwartz multipliers).**

Lean statement: `D5/S3/Analytic/Fourier/ConvolutionL2.schwartz_convolution_l2_multiplier`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ConvolutionL2.schwartz_convolution_l2_multiplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a Schwartz kernel whose Fourier transform has norm at most the nonnegative number B everywhere. For every square-integrable complex f, the concrete convolution k*f is square-integrable and has L² norm at most B times the L² norm of f. The convolution Fourier identity and Schwartz Plancherel give the bound on Schwartz inputs. Schwartz density, the pointwise Hölder convolution bound, and Fatou extend it to every L² input.

**Theorem 1.4 (A real squared Young bound).**

Lean statement: `D5/S3/Analytic/Fourier/ConvolutionL2.real_convolution_l2_young`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ConvolutionL2.real_convolution_l2_young` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a real integrable kernel with integral of its absolute value at most B, where B is nonnegative. For every measurable real f with integrable square, the integral of (k*f)² is at most B² times the integral of f². In particular, the input hypotheses hold for bounded measurable functions supported in a compact interval.

**Theorem 1.5 (Real-valued complex Schwartz kernels).**

Lean statement: `D5/S3/Analytic/Fourier/ConvolutionL2.real_schwartz_convolution_l2_multiplier_of_complex`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ConvolutionL2.real_schwartz_convolution_l2_multiplier_of_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a complex Schwartz kernel k is the complexification of a real function r, and its Fourier transform has norm at most a nonnegative B. For every measurable real f with integrable square, the square of r*f is integrable and its integral is at most B² times the integral of f². The complex convolution multiplier bound supplies square integrability, and taking real parts identifies the real convolution.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/ConvolutionL2.convolution_memLp_two`
- Truth anchor: `D5/S3/Analytic/Fourier/ConvolutionL2.real_convolution_identity`
- Truth anchor: `D5/S3/Analytic/Fourier/ConvolutionL2.real_convolution_l2_young`
- Truth anchor: `D5/S3/Analytic/Fourier/ConvolutionL2.real_schwartz_convolution_l2_multiplier_of_complex`
- Truth anchor: `D5/S3/Analytic/Fourier/ConvolutionL2.schwartz_convolution_l2_multiplier`
