# Continuation

## Abstract

Positive Laplace transforms and paired pole sums admit analytic continuation on right strips.

**Definition 1.1 (A one-sided logarithmic envelope).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.HasLogEnvelope`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.HasLogEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real function has a logarithmic envelope if either it or its negative is bounded above on the nonnegative ray by kappa times log(exp(1)+u) plus C, with kappa and C nonnegative.

**Definition 1.2 (Fejer kernels with bounded Fourier support).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.Admissible`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An admissible pair consists of a Fejer kernel of bandwidth b and its tent Fourier weight with b at most M, or a notched Fejer kernel with notch ordinate U greater than twice b and U+b at most M.

**Definition 1.3 (A weighted measure on the nonnegative ray).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rayMeasure`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rayMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real function q, the ray measure is Lebesgue measure restricted to the nonnegative ray, with density given by the nonnegative extended-real value of q.

**Theorem 1.4 (Weighted exponential integrability).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_integrable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_integrable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For measurable q nonnegative on the nonnegative ray, exp(t*u) is integrable against its ray measure exactly when q(u)*exp(t*u) is Lebesgue integrable on that ray.

**Theorem 1.5 (The moment generating function as a Laplace transform).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_mgf`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_mgf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For measurable q nonnegative on the nonnegative ray, the complex moment generating function of its ray measure at -s equals the Laplace transform of q at s.

**Theorem 1.6 (Nonnegative support of the ray measure).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate is nonnegative almost everywhere with respect to every ray measure.

**Theorem 1.7 (Exponential decay on the nonnegative ray).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.exp_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.exp_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive sigma, exp(-sigma*u) is integrable over the nonnegative ray.

**Theorem 1.8 (Exponentially damped affine functions).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.affine_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.affine_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every affine real function multiplied by exp(-sigma*u) is integrable over the nonnegative ray whenever sigma is positive.

**Theorem 1.9 (Absolute convergence of the complex Laplace integrand).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If q is measurable and q(u)*exp(-Re(s)*u) is integrable over the nonnegative ray, then q(u)*exp(-s*u) is integrable there as a complex function.

**Definition 1.10 (A bounded right strip).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.strip`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.strip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The strip consists of complex s with real part strictly between zero and one and imaginary part of absolute value less than one.

**Definition 1.11 (A finite pole expression for continuation).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a spectrum S and remainder J, the continuation is minus one half of the paired pole sum over ordinates at most eight, plus the regular part with parameter four.

**Theorem 1.12 (Holomorphy of the continued pole expression).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation_holomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation_holomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive spectrum with logarithmic counting asymptotics and paired Laplace data, the finite pole continuation is complex differentiable on the bounded right strip.

**Theorem 1.13 (Agreement on the initial convergence strip).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation_initial`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under logarithmic counting asymptotics and paired Laplace data, the Laplace transform agrees with the finite pole continuation whenever the real part lies strictly between one half and one.

**Theorem 1.14 (Positivity extends Laplace convergence).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.positive_convergence`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.positive_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a measure be supported almost everywhere on the nonnegative ray and suppose its damped exponentials are integrable for every sigma greater than one half. If its complex transform agrees there with a holomorphic function on the bounded right strip, the damped exponentials are integrable for every positive sigma.

**Theorem 1.15 (Holomorphic transforms of nonnegative affine densities).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.affine_mgf_holomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.affine_mgf_holomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An affine density nonnegative on the nonnegative ray has a complex moment generating function at -s that is complex differentiable throughout the bounded right strip.

**Theorem 1.16 (Linearity of convergent Laplace transforms).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_sub_const_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_sub_const_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For measurable a and f whose Laplace integrands are absolutely integrable at s, the Laplace transform of a-e*f equals the transform of a minus e times the transform of f.

**Definition 1.17 (The full right strip).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full right strip consists of all complex numbers whose real parts lie strictly between zero and one.

**Theorem 1.18 (Openness of the full right strip).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip_open`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of complex numbers with real part strictly between zero and one is open.

**Theorem 1.19 (Convexity of the full right strip).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip_convex`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of complex numbers with real part strictly between zero and one is convex over the reals.

**Theorem 1.20 (Holomorphy from absolute Laplace convergence).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_holomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_holomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A measurable real function whose damped integrands are integrable on the nonnegative ray for every positive real parameter has a complex differentiable Laplace transform throughout the full right strip.

**Theorem 1.21 (Holomorphy of the full paired pole sum).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.pole_tsum_holomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.pole_tsum_holomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive spectrum with logarithmic counting asymptotics, the sum of all paired pole terms is complex differentiable throughout the full right strip, away from the poles. At a pole the Lean expression uses the convention 1/0 = 0.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.Admissible`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.HasLogEnvelope`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.affine_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.affine_mgf_holomorphic`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation_holomorphic`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.continuation_initial`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.exp_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_holomorphic`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.laplace_sub_const_mul`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.pole_tsum_holomorphic`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.positive_convergence`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rayMeasure`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_integrable_iff`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_mgf`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.ray_nonneg`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip_convex`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.rightStrip_open`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.strip`
- Dependency: [D5/S3/Analytic/Fourier/AngularFejerKernel](../../Fourier/AngularFejerKernel.md)
- Dependency: [D5/S3/Analytic/Laplace/AbscissaSingularity](../AbscissaSingularity.md)
- Dependency: [D5/S3/Analytic/Laplace/PairedPoleRegularity](../PairedPoleRegularity.md)
