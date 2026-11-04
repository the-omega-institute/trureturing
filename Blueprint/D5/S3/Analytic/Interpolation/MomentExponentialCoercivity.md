# Original full-kernel certificate source

## Abstract

The complete actual-K moment certificate.

**Theorem 1.1 (Division-free Gamma coercivity).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_gamma_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_gamma_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite complex atoms in [0,D], D>=0, lambda>0, and vanishing mass and first moment, let E be the full prefix energy and E_G the ramp energy on [0,D]. Then (E+lambda^2 E_G) Re Q_lambda >= 2lambda E^2. Polarizing the existing square FTC gives the mixed primitive identity; the integral of norm(response-r(prefix-lambda ramp)) squared is nonnegative for every real r. Its discriminant gives E^2<=C H. The causal Gram identity Re Q_lambda=2lambda H+norm(response(D))^2 retains the nonnegative endpoint square. No energy division is used.

**Theorem 1.2 (Nonnegative exponential atomic form).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_kernel_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_kernel_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing causal Gram identity directly gives Re Q_lambda>=0 for every finite complex family supported in [0,D], D>=0 and lambda>0, without a moment hypothesis. This consumed helper permits enlargement of the Gamma denominator and handles the zero-energy branch of the finite head.

**Theorem 1.3 (Gamma coercivity with the actual moment gap).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D>0, q>=1 and atomic moments 0,...,q vanishing, the actual primitive gap delta_q=D^2/(4q(q+1)) gives (1+lambda^2 delta_q) E Re Q_lambda>=2lambda E^2. The Gamma certificate and the consumed primitive-gap supplier apply to the same finite complex family. Empty, repeated, cancelling and zero-energy families remain in scope.

**Theorem 1.4 (moment exponential prefix coercivity).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.moment_exponential_prefix_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.moment_exponential_prefix_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The moment-exponential theorem supplies the quantitative exponential bound. Its existing primitive-gap/causal proof supplies 2lambda(1-lambda^2 delta_q)E as a lower bound for the actual exponential atomic quadratic.

**Theorem 1.5 (causal prefix deficit).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.causal_prefix_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.causal_prefix_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary zero-mass finite complex atoms in [0,D], E-Re Q_exp(1/2) equals one quarter of the integral on [0,D] of the actual resolvent norm squared, plus one quarter of its endpoint norm squared. The owner-local causal Gram and right-FTC square identities prove the normalization directly.

**Theorem 1.6 (exponential prefix deficit nonneg).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_deficit_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_deficit_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding literal causal-square formula gives a nonnegative exponential prefix deficit without a first-moment or spectral premise.

**Theorem 1.7 (actual prefix primitive gap).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.actual_prefix_primitive_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.actual_prefix_primitive_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing complex_L2_moment_primitive_gap is consumed with the actual prefix. Atomic degrees 0,...,q imply prefix degrees 0,...,q-1, yielding integral norm(ramp)^2<=delta_q E. This is reuse-only.

**Theorem 1.8 (growing primitive identity).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.growing_primitive_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.growing_primitive_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal growing-exponential atomic form equals -E+(1/4)integral norm(G)^2+(1/16)H(G), initially with H(G) in causal triangular form. The actual G is integral_0^t prefix and both endpoints vanish. The existing finite causal Gram and primitive-exponential proof bodies require only lambda nonzero, so their telescopes are generalized accordingly and applied at lambda=-1/2. Integrating-factor right FTC identifies the second causal response with the actual growing convolution of G. The square FTC supplies the exact triangle expression; no positivity of the growing exponential is asserted.

**Theorem 1.9 (actual prefix primitive realization).**

Lean statement: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.actual_prefix_primitive_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.actual_prefix_primitive_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The owner right-FTC ramp identity identifies the actual integral primitive at every t>=0 with sum_i a_i max(t-x_i,0), including repeated and endpoint atoms. This is an export of retained proof, consumed by the continuum realization.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.actual_prefix_primitive_gap`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.actual_prefix_primitive_realization`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.causal_prefix_deficit`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_deficit_nonneg`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_gamma_coercivity`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.exponential_prefix_kernel_nonneg`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.growing_primitive_identity`
- Truth anchor: `D5/S3/Analytic/Interpolation/MomentExponentialCoercivity.moment_exponential_prefix_coercivity`
- Dependency: [D5/S3/Analytic/Interpolation/CausalExponentialPrimitive](CausalExponentialPrimitive.md)
- Dependency: [D5/S3/Analytic/MomentOrthogonalPrimitiveGap](../MomentOrthogonalPrimitiveGap.md)
