# Reciprocal-gamma sum identity

## Abstract

Finite reciprocal-gamma convolution and its total kernel.

**Theorem 1.1 (Closed form for the finite convolution).**

Lean statement: `D5/S3/Analytic/KarpZhangGamma/Kernel.reciprocalGamma_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Kernel.reciprocalGamma_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real b,c and every natural m, the sum over k=0,...,m of 1/[k factorial times (m-k) factorial times Real.Gamma(b+k) times Real.Gamma(c+m-k)] equals the evaluation of ascPochhammer at b+c+m-1 in degree m, divided by m factorial times Real.Gamma(b+m) times Real.Gamma(c+m). This is identity (3.11) of the gamma-series argument. It includes m=0 even when b+c-1 is nonpositive.

**Theorem 1.2 (Balancing the Gamma product).**

Lean statement: `D5/S3/Analytic/KarpZhangGamma/Kernel.gamma_balanced_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Kernel.gamma_balanced_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real a and nonnegative real alpha,beta, Real.Gamma(a+alpha) times Real.Gamma(a+beta) is at most Real.Gamma(a) times Real.Gamma(a+alpha+beta). The two interior arguments are complementary convex combinations of the endpoints. Add the two inequalities for log composed with Real.Gamma, then use positivity to exponentiate. If the sum of the shifts is zero the assertion is equality.

**Definition 1.3 (Unpaired scalar kernel).**

Lean statement: `D5/S3/Analytic/KarpZhangGamma/Kernel.kernel`

*Formalization.* `D5/S3/Analytic/KarpZhangGamma/Kernel.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,alpha,beta and natural m,k, kernel(a,alpha,beta,m,k) equals 1/[k factorial times (m-k) factorial] times the difference between 1/[Real.Gamma(a+alpha+k)Real.Gamma(a+beta+m-k)] and 1/[Real.Gamma(a+k)Real.Gamma(a+alpha+beta+m-k)]. Natural subtraction is literal; the theorems sum only over k <= m.

**Theorem 1.4 (Nonnegative total kernel).**

Lean statement: `D5/S3/Analytic/KarpZhangGamma/Kernel.kernel_sum_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangGamma/Kernel.kernel_sum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real a, nonnegative real alpha,beta and natural m, the sum of kernel(a,alpha,beta,m,k) for k=0,...,m is nonnegative. The convolution formula factors this total as the rising-factorial prefactor divided by m factorial, times the reciprocal-gamma balancing difference at a+m. Jensen's inequality for Real.convexOn_log_Gamma makes that difference nonnegative. At m=0 the rising-factorial prefactor is one; at positive degree its argument is positive.

The finite Pascal recurrence and Real.Gamma_add_one prove the convolution identity by induction, simultaneously for every pair of positive parameters. This is a finite Vandermonde recurrence: the two shifted-parameter terms have the same rising-factorial numerator, and their denominator combination supplies its next factor. The total-sum assertion is the scalar input for the finite pairing in Result. Together with the paired sign pattern and coefficientwise exponential smoothing, it gives the two-variable transform inequality.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Kernel.gamma_balanced_shift`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Kernel.kernel`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Kernel.kernel_sum_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangGamma/Kernel.reciprocalGamma_sum`
- Dependency: [D5/S3/Analytic/KarpZhangGamma/Smoothing](Smoothing.md)
