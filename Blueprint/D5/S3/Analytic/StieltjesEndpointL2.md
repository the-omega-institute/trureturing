# Stieltjes endpoint L2 estimate

## Abstract

A pointwise L2 cap controls the integral against the singular Stieltjes weight.

**Definition 1.1 (Interval L2 norm of a real profile).**

Lean statement: `D5/S3/Analytic/StieltjesEndpointL2.l2Norm`

*Formalization.* `D5/S3/Analytic/StieltjesEndpointL2.l2Norm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quantity L_b(q) is the square root of the integral of q(t)^2 from zero to b.

**Definition 1.2 (Stieltjes weight).**

Lean statement: `D5/S3/Analytic/StieltjesEndpointL2.stieltjesWeight`

*Formalization.* `D5/S3/Analytic/StieltjesEndpointL2.stieltjesWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight w(t) is the reciprocal of the real square root of t(1+t).

**Theorem 1.3 (The endpoint split).**

Lean statement: `D5/S3/Analytic/StieltjesEndpointL2.integral_div_sqrt_le_of_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/StieltjesEndpointL2.integral_div_sqrt_le_of_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let b>0 and M≥1, with q continuous and nonnegative on [0,b]. If q(t)≤M L_b(q)/sqrt(b) throughout [0,b], the integral of q(t)/sqrt(t) is at most (2+sqrt(2 log M)) L_b(q). Split at s=b/M^2. The cap and the integral of 1/sqrt(t) give the first piece a bound of 2 L_b(q). On [s,b], Cauchy–Schwarz gives the second piece a bound of sqrt(2 log M) L_b(q) since the squared weight integrates to log(b/s).

**Theorem 1.4 (Weighted norm profile).**

Lean statement: `D5/S3/Analytic/StieltjesEndpointL2.integral_stieltjes_mul_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/StieltjesEndpointL2.integral_stieltjes_mul_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be continuous on [0,b] with values in a normed additive commutative group, where b>0 and M≥1. If q(t)=norm(F(t)) satisfies q(t)≤M L_b(q)/sqrt(b) there, w(t)q(t) is interval integrable and its integral is at most (2+sqrt(2 log M)) L_b(q). On the nonnegative ray the Stieltjes weight is bounded above by 1/sqrt(t).

**Theorem 1.5 (Norm of the Stieltjes integral).**

Lean statement: `D5/S3/Analytic/StieltjesEndpointL2.norm_integral_stieltjes_smul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/StieltjesEndpointL2.norm_integral_stieltjes_smul_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same continuity and cap hypotheses in a complete real normed space, w(t) times F(t) is interval integrable and the norm of its Bochner integral is at most (2+sqrt(2 log M)) L_b(norm(F)). This includes Hilbert-space profiles of the kind used for the short-interval residual in sharp Gibbs recovery.

**Theorem 1.6 (Degree controls the pointwise cap).**

Lean statement: `D5/S3/Analytic/StieltjesEndpointL2.polynomial_norm_le_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/StieltjesEndpointL2.polynomial_norm_le_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural d and a complex polynomial p of degree below d in WithBot(Nat), at every real x in [0,1], norm(p(x))≤(1+d^2) L_1(norm(p)). Evaluation embeds the real input in the complex numbers. The fundamental theorem of calculus bounds each difference p(x)−p(y) by the integral of norm(p'). Averaging in y and applying Cauchy–Schwarz and the canonical complex-polynomial derivative energy estimate gives the cap. The degree condition includes p=0 when d=0.

**Theorem 1.7 (Complex-polynomial Stieltjes bound).**

Lean statement: `D5/S3/Analytic/StieltjesEndpointL2.integral_stieltjes_polynomial_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/StieltjesEndpointL2.integral_stieltjes_polynomial_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural d and a complex polynomial p of degree below d in WithBot(Nat), w(t) norm(p(t)) is interval integrable on [0,1]. Its integral there is at most (2+sqrt(2 log(1+d^2))) L_1(norm(p)). The degree cap supplies M=1+d^2 in the endpoint bound, so the logarithm depends on degree through a polynomial in d.

## References

- Truth anchor: `D5/S3/Analytic/StieltjesEndpointL2.integral_div_sqrt_le_of_pos`
- Truth anchor: `D5/S3/Analytic/StieltjesEndpointL2.integral_stieltjes_mul_norm_le`
- Truth anchor: `D5/S3/Analytic/StieltjesEndpointL2.integral_stieltjes_polynomial_norm_le`
- Truth anchor: `D5/S3/Analytic/StieltjesEndpointL2.l2Norm`
- Truth anchor: `D5/S3/Analytic/StieltjesEndpointL2.norm_integral_stieltjes_smul_le`
- Truth anchor: `D5/S3/Analytic/StieltjesEndpointL2.polynomial_norm_le_cap`
- Truth anchor: `D5/S3/Analytic/StieltjesEndpointL2.stieltjesWeight`
- Dependency: [D5/S3/Analytic/Interpolation/CapWeightedEnergy](Interpolation/CapWeightedEnergy.md)
- Dependency: [D5/S3/Analytic/PolynomialL2Derivative](PolynomialL2Derivative.md)
