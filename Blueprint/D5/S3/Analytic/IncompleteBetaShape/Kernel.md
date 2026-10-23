# Sliding intervals and beta averaging

## Abstract

Affine averages of symmetric beta weights.

**Theorem 1.1 (Reflection of the affine average).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put w(b,y)=[y(1-y)] to the real power b-1. The uniform average F(b,s,v) of w(b,sv+(1-s)u) for u between zero and one is invariant under replacing v by 1-v. Reflection of the uniform integration variable proves this identity.

**Theorem 1.2 (Reflection of the averaged kernel).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function H(c,n,b,v) averages F(b,s,v) against the normalized beta density with shapes c and n+2. It is invariant under reflection of v about one half.

**Theorem 1.3 (Continuity of an affine interval average).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b positive and s between zero, included, and one, excluded, the average F is continuous in v on the closed unit interval. After an affine substitution it is a difference of values of the continuous primitive of the integrable beta weight, divided by 1-s.

**Theorem 1.4 (Control by the complete beta integral).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b positive, s less than one and nonnegative, and v in the closed unit interval, the absolute value of F is at most B(b,b)/(1-s). The affine interval lies inside the unit interval and the weight is nonnegative.

**Theorem 1.5 (Integrability of the averaged weight).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_integrand_intervalIntegrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_integrand_intervalIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive c and b and natural n, the product of F and the unnormalized beta density with shapes c and n+2 is integrable in s for every v in the closed unit interval. The full beta integral bound reduces domination to the integrable density with shapes c and n+1.

**Theorem 1.6 (Continuity through the endpoints).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive c and b the beta averaged kernel H is continuous on the closed unit interval. Dominated convergence uses the same beta majorant for all locations v, including zero and one. This controls the endpoint singularities when b is below one.

**Theorem 1.7 (Boundedness on the unit interval).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive c and b, a finite bound controls the absolute value of H at every location in the closed unit interval.

**Theorem 1.8 (Strict increase toward the midpoint).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_strictMonoOn_of_one_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_strictMonoOn_of_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c positive and b above one, H strictly increases on the interval from zero, excluded, to one half, included. For each s strictly between zero and one, the derivative of F is s/(1-s) times the difference of the beta weight at the right and left endpoints. Their products y(1-y) differ by s(1-s)(1-2v), which is positive before the midpoint. Strict inequalities are integrated in s against a positive density.

**Theorem 1.9 (Strict decrease toward the midpoint).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_strictAntiOn_of_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_strictAntiOn_of_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c positive and b strictly between zero and one, H strictly decreases on the interval from zero, excluded, to one half, included. The negative power reverses the comparison of the endpoint products. Integration preserves the strict comparison without differentiating the averaged kernel.

## References

- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_bound`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_continuousOn`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.F_symm`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_bounded`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_continuousOn`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_integrand_intervalIntegrable`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_strictAntiOn_of_lt_one`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_strictMonoOn_of_one_lt`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Kernel.H_symm`
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
