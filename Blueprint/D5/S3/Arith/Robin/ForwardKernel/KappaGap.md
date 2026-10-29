# Two-sided unboundedness of the complete forward response

## Abstract

Positive logarithmic transforms give two-sided divergence of the complete forward response.

The response T is the complete real-center forward response with window H=x^(4/5). Theta is the supremum of Re(rho) over zeros in the open critical strip. The lower conclusion assumes the explicitly stated Theta error estimate. The upper conclusion additionally assumes Riemann-von Mangoldt for the canonical zeta zero configuration, including its multiplicities. The positive logarithmic budget measure is the pushforward under y=log(x) of the nonnegative density (e*T(x)+k)/x on x>x0. Positive-definite Laplace boundary limits and the exact zeta residues supply the oscillation constraints.

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

**Theorem 1.5 (Arbitrarily large negative excursions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_below`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that for every epsilon>0 there is C such that |psi(t)-t|<=C*t^(Theta+epsilon) for t>=2. For every real L and X there is x>=X with T(x)<L. Under RH, the exponent 3/5 gives a holomorphic remainder across the imaginary axis. An eventual lower bound T(x)>=L defines a nonnegative logarithmic measure whose boundary value at zero is -L. The same-sign budget gives card(Z)<=16*L^2 for every finite set Z of nontrivial zeros. Infinitely many nontrivial zeros contradict this fixed bound. If RH fails, a zero strictly right of the critical line forces negative divergence.

**Theorem 1.6 (The unconditional one-half lower obstruction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_lower_kappa_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_lower_kappa_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the displayed Theta error estimate, for every kappa<1/2 and every real X there exists x>=X with T(x)<-kappa. This follows by taking L=-kappa in the negative-divergence theorem, which also removes the restriction kappa<1/2 from the resulting conclusion.

**Theorem 1.7 (The one-half upper obstruction under RH).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_upper_kappa_gap_of_rh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_upper_kappa_gap_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH and the Theta error estimate, for every K<1/2 and every real X there exists x>=X with T(x)>K. Apply the nonnegative transform to K-T(x); its critical-line residue has the opposite sign and the same absolute value.

**Theorem 1.8 (Failure of RH forces positive divergence).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above_of_not_rh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above_of_not_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the Theta error estimate, failure of RH implies that for all real L and X there exists x>=X with T(x)>L. The functional equation supplies a zero to the right of the critical line. The transform of L-T has a nonzero shifted pole strictly inside its convergence region, which contradicts holomorphy there.

**Theorem 1.9 (Arbitrarily large positive excursions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Theta error estimate and Riemann-von Mangoldt for the canonical zeta zero configuration. For every real L and X there exists x>=X with T(x)>L. Under RH, an eventual bound T(x)<=L makes L-T a positive logarithmic density. Continuity and the nonzero zeta value at one half give a gap around ordinate zero. The quadratic boundary budget bounds the sum of canonical zero multiplicities in every interval shorter than this gap by 4*L^2. Dividing (T,2T] into intervals of half the gap length bounds N(T,2T) by a constant times T+1, contradicting the logarithmic factor in the Riemann-von Mangoldt lower bound. If RH fails, the existing right-hand-zero obstruction gives the conclusion without zero counting.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budgetMeasure_nonnegative`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_exponential_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.budget_transform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_lower_kappa_gap`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_above_of_not_rh`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_below`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_unbounded_below_of_right_zero`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/KappaGap.forward_response_upper_kappa_gap_of_rh`
- Dependency: [D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction](../../../Analytic/Zeta/PositiveLaplacePoleObstruction.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MellinResidue](MellinResidue.md)
- Dependency: [D5/S3/Weil/ZeroData/RiemannVonMangoldtCountGrowth](../../../Weil/ZeroData/RiemannVonMangoldtCountGrowth.md)
- Dependency: [D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction](../../../Weil/ZeroInfinitude/ExplicitFormulaObstruction.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)
- Dependency: [D5/S3/Weil/ZetaRvm/NcountWindow](../../../Weil/ZetaRvm/NcountWindow.md)
