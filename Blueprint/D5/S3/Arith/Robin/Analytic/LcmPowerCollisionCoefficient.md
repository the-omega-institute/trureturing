# Leading coefficients and parameter comparison

## Abstract

Strict increase of the ratio of leading LCM power coefficients.

**Definition 1.1 (Leading coefficient).**

$$\forall kappa \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{c}\left(kappa, x\right) = \frac{\left(x - 1\right) \cdot \left((x)^{kappa - 1} - 1\right)}{\left((x)^{kappa} - 1\right) \cdot \operatorname{log}\left(x\right)}$$

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For real kappa and x define c(kappa,x) by the displayed formula. On kappa>1 and x>1 it is positive. It is the leading coefficient in the large-exponent limit of the LCM power threshold from Definition 4.2.

**Theorem 1.2 (Positivity).**

$$\forall kappa \in \mathbb{R},\; \forall x \in \mathbb{R},\; (1 < kappa \land 1 < x) \Rightarrow (0 < \operatorname{c}\left(kappa, x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.coefficient_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If kappa>1 and x>1, every factor in the defining numerator and denominator is strictly positive. This fact is used in the logarithmic derivative, the leading-term limit, and the comparison at interval endpoints.

**Theorem 1.3 (Strict parameter comparison).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; (\left(1 < p \land p < q\right) \land \left(1 < alpha \land alpha < beta\right)) \Rightarrow (\operatorname{log}\left(\frac{\operatorname{c}\left(alpha, p\right)}{\operatorname{c}\left(alpha, q\right)}\right) < \operatorname{log}\left(\frac{\operatorname{c}\left(beta, p\right)}{\operatorname{c}\left(beta, q\right)}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.log_coefficient_ratio_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For all real bases 1<p<q, the function kappa -> log(c(kappa,p)/c(kappa,q)) is strictly increasing on kappa>1. No primality assumption is needed.

Put s=log(x). The logarithmic derivative in kappa is s/(exp((kappa-1)*s)-1)-s/(exp(kappa*s)-1). The function z/sinh(z) strictly decreases for z>0, since z*cosh(z)-sinh(z) has derivative z*sinh(z)>0 and vanishes at zero. Consequently (s/(2*sinh(v*s/2)))^2 strictly decreases in s for v>0. For s<t, differentiating s/(exp(v*s)-1)-t/(exp(v*t)-1) in v therefore gives a strictly negative derivative. Its value at kappa-1 exceeds its value at kappa. This difference is exactly the derivative of the logarithmic coefficient ratio, proving the claim.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.coefficient`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.coefficient_pos`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.log_coefficient_ratio_strictMono`
