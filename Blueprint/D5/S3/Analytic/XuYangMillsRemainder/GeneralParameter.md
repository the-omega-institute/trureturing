# General-parameter Mills remainder classification

## Abstract

The original general-parameter Mills target, regularity, Gamma coefficients, sharp origin obstruction, strict remainder moment bounds, closed kernel ranges and absolute Laplace control.

**Definition 1.1 (Original signed remainder normalization).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F`

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F n a x is the original signed remainder (-1)^n * D n x a, where D is imported from the frozen Xu-Yang Mills source and retains the Gaussian Mills ratio, Gamma coefficients, and finite truncation.

**Definition 1.2 (Theorem 2.1 target).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21`

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n >= 2 and real a, the positive global-sign predicate is equivalent to complete monotonicity and to a <= theta (n-2); the negative global-sign predicate is equivalent to complete monotonicity of -F and to a >= theta (n-1), with both endpoints included. The proposition is retained as the exact source target.

The proposition states two separate equivalences in each chain: global sign iff complete monotonicity, and complete monotonicity iff the sharp parameter bound. It is a target definition, not an asserted theorem. the exact Laplace representation and the positive sufficiency branch are now proved in the continuation; the infinity asymptotic, sharp negative necessity and complete two-chain theorem remain open.

**Theorem 1.3 (Gaussian regularity and the original origin asymptotic).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.regularity_and_origin`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.regularity_and_origin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n >= 2 and every real a, the original F n a is C-infinity on x > 0, and x^(2n) F n a x tends to -u n a (a-2) as x decreases to zero. The Gaussian tail equals its value at zero minus its interval primitive. The fundamental theorem of calculus gives smoothness of that primitive. After multiplying the finite remainder by x^(2n), every lower truncation term vanishes at zero and only the original nth Gamma coefficient remains.

**Theorem 1.4 (Sharp necessary threshold for the positive branch).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_necessary`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n >= 2 and real a, if the original F n a is completely monotone, then a <= theta (n-2). The proof consumes the zeroth derivative sign and the concrete origin limit. The hypothesis that F is globally nonnegative alone suffices, as established by positive_sign_necessary. The exact general-a Gamma coefficient identity and positivity of B_(n-2) translate u_n <= 0 into the threshold bound.

**Theorem 1.5 (Origin obstruction for the negative branch).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_necessary`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n >= 2 and real a, if -F n a is completely monotone, or merely globally nonnegative, then a >= theta (n-2). This is the obstruction at the origin; it does not establish the required infinity obstruction u (n+1) a (a-2) >= 0 or the sharp negative-branch threshold theta (n-1).

**Theorem 1.6 (Strictly decreasing upper normalized remainder).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.exp_remainder_ratio_strict_anti`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.exp_remainder_ratio_strict_anti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write E_k(y) = (-1)^k (exp(-y) - sum_{j<k} (-y)^j/j!). For every k >= 1, E_k(y)/y^k strictly decreases on y > 0. The proof uses the existing public ExpRemainderDifferences.R with k=r+1, then the pinned Mathlib Taylor integral theorem gives E_k(y)/y^k = integral_0^1 (1-s)^(k-1) exp(-sy) ds / (k-1)!. Strict integral comparison at s=1/2 proves the multiplier order.

**Theorem 1.7 (Strictly increasing lower normalized remainder).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.exp_remainder_ratio_strict_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.exp_remainder_ratio_strict_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k >= 1, E_k(y)/y^(k-1) strictly increases on y > 0. Changing variables in the same Taylor integral gives E_k(y)/y^(k-1) = integral_0^y (1-q/y)^(k-1) exp(-q) dq / (k-1)!. Increasing y increases the integrand on the old interval and adds a strictly positive interval. This includes k=1.

**Theorem 1.8 (Strict exponential remainder moment bounds).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.moment_ratio_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.moment_ratio_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With source remainder order r+1 and z positive, B_r/I_r < M2/M0 < B_(r+1)/I_(r+1). Both M0 and M2 are strictly positive. Apply IncompleteBeta.Comparison.weighted_means_lt to the positive densities E_(r+1)(z(1+v^2)) and (1+v^2)^r for the lower bound, and to (1+v^2)^(r+1) and E_(r+1)(z(1+v^2)) for the upper bound. The two proved normalized remainder orders give the required strict density ratios.

**Theorem 1.9 (Strict inner threshold bounds).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.inner_threshold_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.inner_threshold_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positive moment ratios imply theta_r < (1-M0/M2)/2 < theta_(r+1). Every denominator is strictly positive, including both polynomial moments. The conclusion holds for every r >= 0 and z > 0.

**Theorem 1.10 (Both closed parameter ranges for the signed kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_closed_ranges`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_closed_ranges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For source truncation n=r+2 and every t>0, the kernel L from (2.5) is strictly positive when a <= theta_r and strictly negative when a >= theta_(r+1). Its inner integral is exactly 2 M2 times the difference between the inner threshold and a. The strict inner bounds include both parameter endpoints. This proves the kernel sign ranges. The continuation below proves equality of its Laplace integral with the original F and uses it for both sufficiency branches.

**Theorem 1.11 (Exact general-parameter Gamma coefficient correspondence).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.coefficient_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.coefficient_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r >= 0 and real a, the original u_(r+2)(a,a-2) equals (2r+3)! / (4^(r+1) r!) times (I_r+(2a-1)B_r). The proof directly consumes Result.coeff_sum, Result.intPow_rec and Result.coeff_factorial at their original owner. The same original identities give u_1(a,a-2)=0 for every real a; this removes the first term from the rescaled finite sum. Linearity of the polynomial moment gives B_r=I_(r+1)-I_r. The coefficient is a strictly positive factor times a-theta_r. Both coefficient-sign equivalences include the zero endpoint.

**Theorem 1.12 (Absolute polynomial bound for the signed kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_polynomial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_polynomial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r >= 0, every real a and t >= 0, the absolute value of L r a t is at most (abs(1-2a)+1) t^(2r+5). The source remainder order is r+1. The proof consumes the exact original Result.expRemainderBounds through E r y = Result.expRemainder (r+1) y. The coefficient weight is bounded in absolute value on [0,1], so this estimate holds without a sign restriction on a.

**Theorem 1.13 (Every absolute exponential moment of the signed kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_exponential_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_exponential_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural orders r,m, every real a and every x>0, t^m exp(-xt) L r a t is absolutely integrable on t>0. The polynomial estimate is dominated by the existing exact exponential moment of order m+2r+5. The kernel is continuous for all real t.

**Theorem 1.14 (Exact original Gamma coefficient in the Laplace recurrence).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_laplace_rec`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_laplace_rec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=0, real a and x>0, the Laplace integral of L (r+1) a equals -u_(r+3)(a,a-2)/x^(2r+6) minus the Laplace integral of L r a. The exact original exponential-remainder recurrence gives the polynomial kernel difference. Absolute integrability permits integral subtraction, and the original coefficient_identity identifies the polynomial moment.

**Theorem 1.15 (Exact finite subtraction inside the Laplace integral).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.laplace_finite_subtraction`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.laplace_finite_subtraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=0, real a and x>0, the Laplace integral of L r a equals (-1)^(r+2) times the Laplace integral of the original G_a minus the finite sum of the original (-1)^k u_k(a,a-2)/x^(2k), with 1<=k<=r+2. The base case subtracts u_2/x^4 and uses u_1=0. The exact kernel recurrence then adds each successive Gamma term. All integral subtractions are absolutely integrable. The difference between this expression and the actual F is precisely (-1)^(r+2) times Y_(a,a-2)-(a-1)-Laplace(G_a).

**Theorem 1.16 (Every ordinary derivative of the signed kernel integral).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.signed_kernel_moment_iterated`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.signed_kernel_moment_iterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r,m>=0 and every real a, the mth ordinary derivative of the Laplace integral of L r a equals the integral of (-t)^m exp(-xt) L r a t for x>0. No positivity assumption on the kernel or parameter is used. On y>x/2, the absolute derivative integrand is dominated by (abs(1-2a)+1) t^(m+2r+6) exp(-xt/2), an integrable exponential moment. Repeated dominated differentiation also gives C-infinity regularity of this integral.

**Theorem 1.17 (The exact outstanding Gaussian term in every derivative of the original F).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.all_order_laplace_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.all_order_laplace_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every derivative order m including zero, the mth derivative of the original F_(r+2,a) equals the signed-kernel moment plus the mth derivative of (-1)^(r+2) [Y_(a,a-2)-(a-1)-Laplace(G_a)]. The finite-subtraction identity and smoothness justify this equality on x>0. The Gaussian identity is discharged in the continuation below. The remaining open obligations are the infinity asymptotic, sharp negative necessity and assembly of the complete two-chain classification.

**Theorem 1.18 (General-parameter Gaussian convolution kernel identity).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_kernel_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_kernel_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a and t, the source kernel G_a(t) equals t^3/4 times the integral from zero to one of (1+(2a-1)v^2) exp(-(1+v^2)t^2/4). Integrating the derivative of v exp(-(1+v^2)t^2/4) gives exp(-t^2/2) as the integral of (1-t^2 v^2/2) times the same exponential. Substitution in G and linearity of the integral give the stated identity. This is the source's pointwise identity (2.3).

**Theorem 1.19 (The negative-parameter Gaussian kernel is the original K kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_kernel_eq_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_kernel_eq_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A second interval integration by parts gives G_(-1)(t)=K(t), preserving the original Gaussian convolution normalization and the exact K supplier.

**Theorem 1.20 (The exact general-parameter Gaussian Laplace identity).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_laplace_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_laplace_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Mills Laplace formula and square convolution are combined with the original kernelLaplace identity at parameter -1. A direct integration by parts gives the t times Gaussian integral, and linearity in a then yields Y_(a,a-2)(x)-(a-1)=integral exp(-xt) G_a(t) for every x>0.

**Theorem 1.21 (The exact Laplace representation of the original F).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of the Gaussian identity into the finite-subtraction defect removes the residual exactly, giving F_(r+2,a)(x)=integral exp(-xt)L_(r,a)(t).

**Theorem 1.22 (Every ordinary derivative of the original F).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_iterated_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_iterated_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact Laplace representation and the signed-kernel iterated differentiation theorem give the integral of (-t)^m exp(-xt)L for every ordinary order m, including zero.

**Theorem 1.23 (Positive complete-monotonicity sufficiency with the closed endpoint).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_sufficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive closed kernel range, exact F Laplace representation and all-order derivative formula prove complete monotonicity whenever a <= theta_(n-2), including equality.

**Theorem 1.24 (Negative complete-monotonicity sufficiency with the closed endpoint).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_sufficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative closed kernel range, exact F Laplace representation and all-order derivative formula prove complete monotonicity of -F whenever a >= theta_(n-1), including equality. The converse still requires the infinity asymptotic.

## References

- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_iterated_deriv`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_laplace`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.all_order_laplace_defect`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.coefficient_identity`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.exp_remainder_ratio_strict_anti`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.exp_remainder_ratio_strict_mono`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_kernel_eq_K`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_kernel_identity`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.gaussian_laplace_identity`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.inner_threshold_bounds`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_closed_ranges`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_exponential_moments`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_laplace_rec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_polynomial_bound`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.laplace_finite_subtraction`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.moment_ratio_bounds`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_necessary`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_sufficiency`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_necessary`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_sufficiency`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.regularity_and_origin`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.signed_kernel_moment_iterated`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Comparison](../IncompleteBeta/Comparison.md)
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/Result](Result.md)
