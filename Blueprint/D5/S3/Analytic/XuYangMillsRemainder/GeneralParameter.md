# General-parameter Mills remainder classification

## Abstract

Original Mills normalization and complete classification.

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

For every n >= 2 and real a, the positive global-sign predicate is equivalent to complete monotonicity and to a <= theta (n-2); the negative global-sign predicate is equivalent to complete monotonicity of -F and to a >= theta (n-1), with both endpoints included. The proposition is the exact original source target.

The proposition states two separate equivalences in each chain: global sign iff complete monotonicity, and complete monotonicity iff the sharp parameter bound. The theorem result proves this entire proposition using the original Gaussian Mills ratio, Gamma coefficients and finite subtraction. Complete monotonicity includes C-infinity regularity and every ordinary derivative order, including zero.

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

**Theorem 1.5 (Strict exponential remainder moment bounds).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.moment_ratio_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.moment_ratio_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With source remainder order r+1 and z positive, B_r/I_r < M2/M0 < B_(r+1)/I_(r+1). Both M0 and M2 are strictly positive. Apply IncompleteBeta.Comparison.weighted_means_lt to the positive densities E_(r+1)(z(1+v^2)) and (1+v^2)^r for the lower bound, and to (1+v^2)^(r+1) and E_(r+1)(z(1+v^2)) for the upper bound. The two proved normalized remainder orders give the required strict density ratios.

**Theorem 1.6 (Strict inner threshold bounds).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.inner_threshold_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.inner_threshold_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positive moment ratios imply theta_r < (1-M0/M2)/2 < theta_(r+1). Every denominator is strictly positive, including both polynomial moments. The conclusion holds for every r >= 0 and z > 0.

**Theorem 1.7 (Both closed parameter ranges for the signed kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_closed_ranges`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_closed_ranges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For source truncation n=r+2 and every t>0, the kernel L from (2.5) is strictly positive when a <= theta_r and strictly negative when a >= theta_(r+1). Its inner integral is exactly 2 M2 times the difference between the inner threshold and a. The strict inner bounds include both parameter endpoints. The exact equality of its Laplace integral with the original F gives both complete-monotonicity sufficiency branches.

**Theorem 1.8 (Exact general-parameter Gamma coefficient correspondence).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.coefficient_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.coefficient_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r >= 0 and real a, the original u_(r+2)(a,a-2) equals (2r+3)! / (4^(r+1) r!) times (I_r+(2a-1)B_r). The proof directly consumes Result.coeff_sum, Result.intPow_rec and Result.coeff_factorial at their original owner. The same original identities give u_1(a,a-2)=0 for every real a; this removes the first term from the rescaled finite sum. Linearity of the polynomial moment gives B_r=I_(r+1)-I_r. The coefficient is a strictly positive factor times a-theta_r. Both coefficient-sign equivalences include the zero endpoint.

**Theorem 1.9 (Absolute polynomial bound for the signed kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_polynomial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_polynomial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r >= 0, every real a and t >= 0, the absolute value of L r a t is at most (abs(1-2a)+1) t^(2r+5). The source remainder order is r+1. The proof consumes the exact original Result.expRemainderBounds through E r y = Result.expRemainder (r+1) y. The coefficient weight is bounded in absolute value on [0,1], so this estimate holds without a sign restriction on a.

**Theorem 1.10 (Every absolute exponential moment of the signed kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_exponential_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_exponential_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural orders r,m, every real a and every x>0, t^m exp(-xt) L r a t is absolutely integrable on t>0. The polynomial estimate is dominated by the existing exact exponential moment of order m+2r+5. The kernel is continuous for all real t.

**Theorem 1.11 (Exact original Gamma coefficient in the Laplace recurrence).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_laplace_rec`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_laplace_rec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=0, real a and x>0, the Laplace integral of L (r+1) a equals -u_(r+3)(a,a-2)/x^(2r+6) minus the Laplace integral of L r a. The exact original exponential-remainder recurrence gives the polynomial kernel difference. Absolute integrability permits integral subtraction, and the original coefficient_identity identifies the polynomial moment.

**Theorem 1.12 (Exact finite subtraction inside the Laplace integral).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.laplace_finite_subtraction`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.laplace_finite_subtraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=0, real a and x>0, the Laplace integral of L r a equals (-1)^(r+2) times the Laplace integral of the original G_a minus the finite sum of the original (-1)^k u_k(a,a-2)/x^(2k), with 1<=k<=r+2. The base case subtracts u_2/x^4 and uses u_1=0. The exact kernel recurrence then adds each successive Gamma term. All integral subtractions are absolutely integrable. The difference between this expression and the actual F is precisely (-1)^(r+2) times Y_(a,a-2)-(a-1)-Laplace(G_a).

**Theorem 1.13 (Every ordinary derivative of the signed kernel integral).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.signed_kernel_moment_iterated`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.signed_kernel_moment_iterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r,m>=0 and every real a, the mth ordinary derivative of the Laplace integral of L r a equals the integral of (-t)^m exp(-xt) L r a t for x>0. No positivity assumption on the kernel or parameter is used. On y>x/2, the absolute derivative integrand is dominated by (abs(1-2a)+1) t^(m+2r+6) exp(-xt/2), an integrable exponential moment.

**Theorem 1.14 (The exact Laplace representation of the original F).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of the Gaussian identity into the finite-subtraction defect removes the residual exactly, giving F_(r+2,a)(x)=integral exp(-xt)L_(r,a)(t).

**Theorem 1.15 (Every ordinary derivative of the original F).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_iterated_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_iterated_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact Laplace representation and the signed-kernel iterated differentiation theorem give the integral of (-t)^m exp(-xt)L for every ordinary order m, including zero.

**Theorem 1.16 (Positive complete-monotonicity sufficiency with the closed endpoint).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_sufficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive closed kernel range, exact F Laplace representation and all-order derivative formula prove complete monotonicity whenever a <= theta_(n-2), including equality.

**Theorem 1.17 (Negative complete-monotonicity sufficiency with the closed endpoint).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_sufficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative closed kernel range, exact F Laplace representation and all-order derivative formula prove complete monotonicity of -F whenever a >= theta_(n-1), including equality.

**Theorem 1.18 (A quantitative bound for every original remainder).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=0, real a and x>0, the absolute value of F_(r+2,a)(x) is at most (abs(1-2a)+1) (2r+5)! / x^(2r+6). Integral norm comparison applies the signed-kernel polynomial bound and the exact original exponential moment. Consequently x^(2r+4) F_(r+2,a)(x) tends to zero at infinity, with an absolute bound equal to a fixed constant times x^(-2).

**Theorem 1.19 (The original infinity asymptotic with its exact Gamma coefficient).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.infinity_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.infinity_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=2 and real a, x^(2n+2) F_(n,a)(x) tends to -u_(n+1)(a,a-2) at infinity. The exact finite Laplace recurrence gives F_(n+1,a)=-u_(n+1)/x^(2n+2)-F_(n,a). The quantitative next-remainder bound makes x^(2n+2) F_(n+1,a) tend to zero. This proves the source's limit (2.12) in the original normalization.

**Theorem 1.20 (Sharp negative necessity already from the global sign).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_sign_sharp_necessary`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_sign_sharp_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If -F_(n,a) is globally nonnegative on x>0, its rescaled infinity limit is nonnegative. Thus u_(n+1)(a,a-2)>=0, and the exact coefficient identity with positive B_(n-1) gives a>=theta_(n-1), including equality.

**Theorem 1.21 (Complete original Theorem 2.1).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer n>=2 and every real a, global nonnegativity of the original F_(n,a) is equivalent to its complete monotonicity and to a<=theta_(n-2). Global nonnegativity of -F_(n,a) is equivalent to complete monotonicity of -F_(n,a) and to a>=theta_(n-1). Both endpoints are included. The positive necessity comes from the origin limit; the negative necessity comes from the infinity limit. The exact signed Laplace formula supplies both sufficient conditions and every ordinary derivative sign, including order zero. The original Mills ratio, Gamma coefficients, D_n and integral thresholds are retained.

## References

- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_bound`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_iterated_deriv`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.actual_f_laplace`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.coefficient_identity`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.infinity_endpoint`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.inner_threshold_bounds`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_closed_ranges`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_exponential_moments`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_laplace_rec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.kernel_polynomial_bound`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.laplace_finite_subtraction`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.moment_ratio_bounds`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_cm_sufficiency`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.negative_sign_sharp_necessary`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_necessary`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.positive_cm_sufficiency`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.regularity_and_origin`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.result`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.signed_kernel_moment_iterated`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Comparison](../IncompleteBeta/Comparison.md)
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace](GaussianLaplace.md)
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders](NormalizedRemainderOrders.md)
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/Result](Result.md)
