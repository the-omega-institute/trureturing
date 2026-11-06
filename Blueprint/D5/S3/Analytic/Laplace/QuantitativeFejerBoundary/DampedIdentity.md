# Damped convolution identities

## Abstract

Fourier inversion and damping limits control convolutions with admissible Fejer kernels.

**Theorem 1.1 (Continuity of the tent weight).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.phi_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.phi_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fejer tent Fourier weight is continuous for every real bandwidth.

**Theorem 1.2 (Vanishing outside the bandwidth).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.phi_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.phi_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive b, the Fejer tent weight vanishes at every t with absolute value at least b.

**Theorem 1.3 (Continuity, positivity and Fourier support).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive bandwidth, an admissible kernel and its weight are continuous and integrable, the kernel is nonnegative, its angular Fourier transform equals the weight, and the weight vanishes outside the prescribed interval.

**Theorem 1.4 (Fourier inversion for a damped convolution).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_fubini`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_fubini` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be continuous and integrable, with integrable angular Fourier transform w. If q(u)*exp(-sigma*u) is integrable on the nonnegative ray, the damped convolution with g equals one over two pi times the integral of w(t), the Laplace transform at sigma+i*t, and exp(i*t*y).

**Definition 1.5 (The finite spectral cosine polynomial).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral pole polynomial at M is minus the sum of multiplicity times cos(gamma*u) over positive ordinates at most twice M.

**Theorem 1.6 (Continuity of the spectral polynomial).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite spectral cosine polynomial is continuous on the real line.

**Theorem 1.7 (Absolute Laplace convergence of the spectral polynomial).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_convergence`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite spectral cosine polynomial multiplied by exp(-sigma*u) is integrable on the nonnegative ray for every positive sigma.

**Theorem 1.8 (The Laplace transform of the spectral polynomial).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex s with positive real part, the Laplace transform of the finite spectral cosine polynomial is minus one half of the paired pole sum over ordinates at most twice M.

**Definition 1.9 (A sequence of damping parameters).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping`

*Formalization.* `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth damping parameter is one over twice the quantity n+1.

**Theorem 1.10 (Positive damping parameters).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every term of the damping sequence is strictly positive.

**Theorem 1.11 (Damping parameters below one).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every term of the damping sequence is strictly less than one.

**Theorem 1.12 (Removal of damping from an integrable function).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_integral_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_integral_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real function integrable on the nonnegative ray, the integrals after multiplication by exp(-damping(n)*u) converge to its original integral.

**Theorem 1.13 (Integrable logarithmic kernel averages).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_log_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_log_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an admissible kernel of positive bandwidth and y at least one, the function g(y-u)*log(exp(1)+u) is integrable over the nonnegative ray.

**Theorem 1.14 (Boundary convergence of the regular part).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.regular_integral_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.regular_integral_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For logarithmic spectral counting asymptotics, paired Laplace data, continuous w and M at least four, the integrals over [-M,M] of w(t) times the regular part at damping(n)+i*t times exp(i*t*y) converge to the corresponding boundary integral at i*t.

**Theorem 1.15 (A uniform pointwise bound for the kernels).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible kernel of positive bandwidth b has absolute value at most b divided by pi at every real argument.

**Theorem 1.16 (Bounding the polynomial by spectral mass).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute value of the finite spectral cosine polynomial at every real argument is at most the spectral counting mass at twice M.

**Theorem 1.17 (Real and complex forms of a damped integral).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_cast_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_cast_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real q and g, the complex integral of q(u)*exp(-sigma*u)*g(y-u) over the nonnegative ray equals the complex embedding of the corresponding real integral.

**Theorem 1.18 (Integrability from a one-sided majorant and damping limits).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.integrable_of_one_sided_damping`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.integrable_of_one_sided_damping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q and a be measurable on the real line, with a integrable on the nonnegative ray, and let e have absolute value one. If e*q is bounded above by a on that ray, all damped versions of q are integrable there, and their integrals converge to a finite real limit, then q is integrable there.

**Theorem 1.19 (The negative-ray truncation error).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_truncation_error`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_truncation_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an admissible kernel of positive bandwidth and positive y, the absolute difference between its nonnegative-ray convolution with the spectral polynomial and the full Fourier-weighted cosine sum is at most the spectral mass at twice M times four divided by pi*b*y.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_bounded`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_laws`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.admissible_log_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_cast_integral`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_fubini`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damped_integral_tendsto`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping_lt_one`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.damping_pos`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.integrable_of_one_sided_damping`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.phi_continuous`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.phi_eq_zero`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_bound`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_continuous`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_convergence`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_laplace`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.polePolynomial_truncation_error`
- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.regular_integral_tendsto`
- Dependency: [D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation](Continuation.md)
