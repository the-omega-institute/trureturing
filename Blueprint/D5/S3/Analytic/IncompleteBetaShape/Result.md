# Coefficient convolution and shape imbalance

## Abstract

Strict coefficient signs for real shifts of the first incomplete beta parameter.

**Theorem 1.1 (Strict decrease with imbalance above one).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictAnti_imbalance`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictAnti_imbalance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

Let m be positive, n natural, and b greater than one. The sum over k from zero through n of c(k,m+d,b)c(n-k,m-d,b) strictly decreases as d ranges from zero, included, to m, excluded. The affine beta-mixture representation gives a common positive factor at fixed 2m. Its remaining factor is the beta mean of the continuous symmetric kernel H, which strictly increases toward its midpoint. The existing beta-mean comparison therefore gives strict decrease with the imbalance d.

**Theorem 1.2 (Strict increase with imbalance below one).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictMono_imbalance`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictMono_imbalance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

When b lies strictly between zero and one, the same convolution strictly increases with d. The function -H is continuous, symmetric, and strictly increasing toward the midpoint, so it satisfies the beta-mean comparison hypotheses. Linearity of the integral reverses the resulting inequality for H.

**Theorem 1.3 (The strict coefficient signs).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-2016-incomplete-beta-first-parameter-coefficient-signs` (proved) by `D5/S3/Analytic/IncompleteBetaShape/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-2016-incomplete-beta-first-parameter-coefficient-signs","declaration_gid":"D5/S3/Analytic/IncompleteBetaShape/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

For all positive real a, b, alpha and beta, and every natural n, the coefficient psi(n) is strictly negative when b is less than one and strictly positive when b is greater than one. Here c(j,t,b) is Gamma(t+b+j) divided by Gamma(b)Gamma(t+j+1), and psi(n) sums c(k,a+alpha,b)c(n-k,a+beta,b) minus c(k,a,b)c(n-k,a+alpha+beta,b) over k from zero through n. The coefficients are independent of x, so these signs give strict coefficient-wise Wright log-convexity below one and strict coefficient-wise Wright log-concavity above one for the normalized incomplete beta series.

Both parameter pairs have mean m=a+(alpha+beta)/2. Their nonnegative half-differences are |alpha-beta|/2 and (alpha+beta)/2. Positivity of both shifts makes the first strictly smaller. The convolution comparison, together with commutativity of the finite convolution, gives the two signs without restricting either shift to integers.

## References

- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictAnti_imbalance`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictMono_imbalance`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Result.result`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Comparison](../IncompleteBeta/Comparison.md)
- Dependency: [D5/S3/Analytic/IncompleteBetaShape/Kernel](Kernel.md)
- Dependency: [D5/S3/Analytic/IncompleteBetaShape/Mixture](Mixture.md)
