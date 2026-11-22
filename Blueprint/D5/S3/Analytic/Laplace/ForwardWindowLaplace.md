# Laplace transform of a forward window

## Abstract

A forward integral window multiplies the tail Laplace transform and subtracts a finite cutoff correction.

Let g be real-valued and let L(z) denote its tail Laplace transform with cutoff U and kernel exp(−zt). The window uses times ahead of its starting time t, which gives the positive sign in the exponent of the multiplier.

**Definition 1.1 (Forward window integral).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow`

*Formalization.* `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The window at t is Wₕg(t)=∫ over (0,h] of g(t+v) dv.

**Theorem 1.2 (Interval integral for nonnegative widths).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow_eq_intervalIntegral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow_eq_intervalIntegral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If h≥0, then Wₕg(t)=∫₀ʰ g(t+v) dv.

**Definition 1.3 (Window multiplier).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier`

*Formalization.* `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The multiplier Mₕ(z) is the integral of exp(zv) over (0,h].

**Definition 1.4 (Finite cutoff correction).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowCorrection`

*Formalization.* `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction Q(z) is the integral over t∈(U−h,U] of exp(−zt) times the integral of g over (U,t+h]. It is the contribution from starting the window below U after extending g by zero on (−∞,U].

**Theorem 1.5 (Entire multiplier).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real width h, the function Mₕ is entire.

**Theorem 1.6 (Closed form of the multiplier).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_eq_div`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_eq_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h≥0 and z≠0, Mₕ(z)=(exp(zh)−1)/z.

**Theorem 1.7 (Nonvanishing off the imaginary axis).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_ne_zero_of_re_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_ne_zero_of_re_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If h>0 and Re(z)≠0, then Mₕ(z)≠0 since |exp(zh)|=exp(h Re(z))≠1.

**Theorem 1.8 (Entire cutoff correction).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowCorrection_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowCorrection_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If h≥0 and g is integrable on (U,U+h], the finite cutoff correction Q is entire.

**Theorem 1.9 (Integrability of the complex kernel).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.kernel_integrable_of_real_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.kernel_integrable_of_real_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If exp(−Re(z)t)g(t) is integrable on (U,∞), so is exp(−zt)g(t). The two integrands have the same absolute value.

**Theorem 1.10 (Transform identity at a convergent parameter).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.tailLaplace_forwardWindow`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.tailLaplace_forwardWindow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If h≥0 and exp(−zt)g(t) is integrable on (U,∞), the window kernel is also integrable there. Its tail transform is Mₕ(z)L(z)−Q(z). Extend g by zero below U, interchange the absolutely integrable window and tail integrals, and subtract the contribution for starts in (U−h,U].

**Theorem 1.11 (Transform identity on the right half-plane).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow_laplace_halfPlane`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow_laplace_halfPlane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If h>0 and exp(−xt)g(t) is integrable on (U,∞) for each real x>0, then Q is entire and the window transform converges absolutely and equals Mₕ(z)L(z)−Q(z) for every z with Re(z)>0.

**Theorem 1.12 (First moment as a negative derivative).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.tailLaplace_firstMoment_eq_neg_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.tailLaplace_firstMoment_eq_neg_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the derivative at s of the tail transform F of f is given by −∫ over (U,∞) of t exp(−st)f(t) dt, then the tail transform of t↦t f(t) at s equals −F′(s).

**Theorem 1.13 (Euler equation for the first moment).**

Lean statement: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.neg_deriv_euler_of_first_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/ForwardWindowLaplace.neg_deriv_euler_of_first_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose F is analytic at s and the identities zF″(z)+2F′(z)=Φ(z) and L(z)=−F′(z) hold as germs at s. Differentiation gives sL″(s)+3L′(s)=−Φ′(s).

## References

- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow_eq_intervalIntegral`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.forwardWindow_laplace_halfPlane`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.kernel_integrable_of_real_weight`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.neg_deriv_euler_of_first_moment`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.tailLaplace_firstMoment_eq_neg_deriv`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.tailLaplace_forwardWindow`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowCorrection`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowCorrection_entire`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_entire`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_eq_div`
- Truth anchor: `D5/S3/Analytic/Laplace/ForwardWindowLaplace.windowMultiplier_ne_zero_of_re_ne_zero`
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](EulerPoleObstruction.md)
