# One-half gaps for the complete forward response

## Abstract

Positive logarithmic transforms give one-sided oscillation bounds for the complete forward response.

The response T is the complete real-center forward response with window H=x^(4/5). Theta is the supremum of Re(rho) over zeros in the open critical strip. The only unproved analytic number-theory input is the explicitly stated Theta error estimate. The positive logarithmic budget measure is the pushforward under y=log(x) of the nonnegative density (e*T(x)+k)/x on x>x0. Nonnegative Laplace-transform boundary singularities and the exact zeta residues supply the oscillation constraints.

**Theorem 1.1 (Nonnegative logarithmic support).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budgetMeasure_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budgetMeasure_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x0>=1, the pushforward by the real logarithm of the measure with density (e*T(x)+k)/x on x>x0 is supported on nonnegative real numbers. The density is read through its nonnegative part.

**Theorem 1.2 (An initial convergence half-plane).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_exponential_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_exponential_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha>=0 and assume |psi(t)-t|<=C*t^alpha eventually. Suppose x0>=3 and e*T(x)+k>=0 for x>=x0. The positive logarithmic budget measure has a finite exponential integral at every Laplace parameter sigma>max(0,alpha-3/10).

**Theorem 1.3 (The exact positive budget transform).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, the complex moment-generating function of the budget measure at -s equals e*F(s)+k*x0^(-s)/s for Re(s)>max(0,alpha-3/10). Here F is the Mellin integral of the complete forward response. The logarithmic pushforward and the density x^(-1) retain the exact Mellin Jacobian.

**Theorem 1.4 (A right-hand zero forces negative divergence).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_below_of_right_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_below_of_right_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Theta be the supremum of the real parts of the nontrivial zeta zeros. Assume that for every epsilon>0 there is C with |psi(t)-t|<=C*t^(Theta+epsilon) for t>=2. If some nontrivial zero has real part greater than one half, then for all real L and X there exists x>=X with T(x)<L. A zero can be selected with beta>max(1/2,Theta-1/5); a sufficiently small positive epsilon places its shifted pole strictly inside the positive-transform convergence region.

**Theorem 1.5 (The unconditional one-half lower obstruction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_lower_kappa_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_lower_kappa_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the displayed Theta error estimate, for every kappa<1/2 and every real X there exists x>=X with T(x)<-kappa. In the RH case, any nontrivial zero lies on the critical line and its Mellin residue has absolute value at least one half. Positivity bounds this residue by the assumed eventual lower budget. Outside RH the stronger negative-divergence theorem applies.

**Theorem 1.6 (The one-half upper obstruction under RH).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_upper_kappa_gap_of_rh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_upper_kappa_gap_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH and the Theta error estimate, for every K<1/2 and every real X there exists x>=X with T(x)>K. Apply the nonnegative transform to K-T(x); its critical-line residue has the opposite sign and the same absolute value.

**Theorem 1.7 (Failure of RH forces positive divergence).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above_of_not_rh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above_of_not_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the Theta error estimate, failure of RH implies that for all real L and X there exists x>=X with T(x)>L. The functional equation supplies a zero to the right of the critical line. The transform of L-T has a nonzero shifted pole strictly inside its convergence region, which contradicts holomorphy there.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budgetMeasure_nonnegative`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_exponential_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_transform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_lower_kappa_gap`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above_of_not_rh`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_below_of_right_zero`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_upper_kappa_gap_of_rh`
- Dependency: [D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction](../../../Analytic/Zeta/PositiveLaplacePoleObstruction.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MellinResidue](MellinResidue.md)
- Dependency: [D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction](../../../Weil/ZeroInfinitude/ExplicitFormulaObstruction.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)
