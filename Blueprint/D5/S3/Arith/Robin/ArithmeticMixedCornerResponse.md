# The Actual Arithmetic Mixed Response

## Abstract

Actual coprime integer corners equal a strictly positive curvature integral with explicit area bounds.

**Definition 1.1 (The absolute logarithmic Robin margin).**

Lean statement: `D5/S3/Arith/Robin/ArithmeticMixedCornerResponse.G`

*Formalization.* `D5/S3/Arith/Robin/ArithmeticMixedCornerResponse.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G(n)=log(sigma_1(n)/n)-gamma-log(log(log(n))), where gamma is Euler's constant and all logarithms are real natural logarithms. For n>=3 every logarithm argument used here is positive. In particular G(n)<0 is the strict Robin sign on this domain.

**Theorem 1.2 (Exact transport and quantitative curvature).**

$$\forall n \in \mathbb{N}, r \in \mathbb{N}, s \in \mathbb{N},\; \left(\left(\left(3 \le n \land 2 \le r\right) \land 2 \le s\right) \land \operatorname{gcd}\left(r, s\right) = 1\right) \Rightarrow \left(\left(\left(\left(\left(\left(1 < \operatorname{log}\left(n\right) \land 0 < \operatorname{log}\left(r\right)\right) \land 0 < \operatorname{log}\left(s\right)\right) \land \operatorname{J}\left(n, r, s\right) = \int_{0}^{\operatorname{log}\left(r\right)} \int_{0}^{\operatorname{log}\left(s\right)} \operatorname{k}\left(\operatorname{log}\left(n\right) + u + v\right) dv du\right) \land 0 < \operatorname{J}\left(n, r, s\right)\right) \land \operatorname{log}\left(r\right) \cdot \operatorname{log}\left(s\right) \cdot \operatorname{k}\left(\operatorname{log}\left(n\right) + \operatorname{log}\left(r\right) + \operatorname{log}\left(s\right)\right) \le \operatorname{J}\left(n, r, s\right)\right) \land \operatorname{J}\left(n, r, s\right) \le \operatorname{log}\left(r\right) \cdot \operatorname{log}\left(s\right) \cdot \operatorname{k}\left(\operatorname{log}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ArithmeticMixedCornerResponse.arithmetic_mixed_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed statement x=log(n), a=log(r), b=log(s), J(n,r,s)=G(n*r*s)+G(n)-G(n*r)-G(n*s), and k(t)=(log(t)+1)/(t^2*log(t)^2). The function k is exactly D5/S3/Arith/Robin/ActualRobinClockCovariance.activationDensity. The theorem also proves x>1, a>0 and b>0. Coprimality is required only between r and s; either or both may share prime factors with n. Thus r=p^i and s=q^j are included for distinct primes p,q and arbitrary positive exponents i,j, including p|n and q|n.

The arithmetic proof computes gcd(n*r,n*s)=n and lcm(n*r,n*s)=n*r*s. It directly applies Mathlib's ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply to sigma_1. After normalization by the integer arguments, the four log(sigma_1/n) terms cancel; gamma cancels as well. The remaining log-log rectangle is integrated twice using the existing D5/S3/Arith/Robin/ActualRobinClockCovariance.density_integral and Mathlib integral_inv_div_log. Monotonicity of k follows from D5/S3/Arith/Robin/MellinWeightedVariation.scaleWeight_antitone. The endpoint kernel comparisons are integrated over both intervals, giving the area bounds and strict positivity without a response-bound premise.

The finite response is described in the thermodynamic-action theory, section 16.1, and seams theory, sections 8 through 10. The existing D5/S3/Arith/Robin/LogLogHigherDerivative.signed_iteratedDeriv_logLog_pos supplies higher analytic signs but does not assert this arithmetic transport.

For n>=3 and the literal five-state menu (n,p*n,q*n,r*n,p*r*n), take d=(G(n),G(p*n),G(q*n),G(r*n),G(p*r*n)), beta>0, and P_s=exp(beta*d_s)/sum_t exp(beta*d_t), with s,t in Fin 5. The definition D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.hiddenChi gives hiddenChi(P)=beta*(G(p*r*n)+G(n)-G(p*n)-G(r*n))=beta*J(n,p,r)>0 for distinct primes p,r and any chosen prime q; the q slot does not enter this contrast. Commutativity identifies the displayed integer addresses with the theorem's corners. D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart places this law in its global visible-occupancy and hidden-coordinate chart.

Keep the absolute log partition A0=log(sum_s exp(beta*d_s)). For normalized weights P_s, d_s=(log(P_s)+A0)/beta. The mixed contrast cancels A0, but an absolute Robin sign still needs it. This positive finite response supplies no absolute Robin anchor, menu-external integer control, cofinal tail estimate or strict global margin. The multipliers include prime powers; positivity of their mixed response does not establish their absolute signs. Strict Robin for every n>5040 and RH remain unproved.

## References

- Truth anchor: `D5/S3/Arith/Robin/ArithmeticMixedCornerResponse.G`
- Truth anchor: `D5/S3/Arith/Robin/ArithmeticMixedCornerResponse.arithmetic_mixed_response`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/LogLogHigherDerivative](LogLogHigherDerivative.md)
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
- Dependency: [D5/S3/Arith/Robin/PrimeFiberPropagation](PrimeFiberPropagation.md)
