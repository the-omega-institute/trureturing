# Bernoulli lower bound for the LCM local factor

## Abstract

The normalized prime-power local factor is bounded below by the Euler factor and a uniform Bernoulli correction.

**Definition 1.1 (Normalized local factor).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.normalizedLocalFactor`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.normalizedLocalFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real kappa, r, and a this is the normalized local difference (1-r)^(-kappa) ((1-r^(a+1))^kappa-r^kappa(1-r^a)^kappa).

**Definition 1.2 (Uniform correction coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.localFactorConstant`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.localFactorConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is c_kappa=kappa/(1-(1/2)^kappa), the uniform replacement for kappa/(1-r^kappa) when 0<=r<=1/2.

**Theorem 1.3 (Local factor lower bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.local_factor_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.local_factor_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1<=kappa, 0<=r<=1/2, and 1<=a, the normalized local factor is at least (1-r)^(-kappa)(1-r^kappa)(1-c_kappa*r^(a+1)).

The proof uses the tangent-line Bernoulli inequality for the convex map u ↦ u^kappa, the bound (1-r^a)^kappa<=1, and monotonicity of real powers to obtain the uniform coefficient. It isolates the local algebraic core and makes no claim about later Euler products or RH.

The Reg source-bound escape audit remains unresolved with unclassified_form:source.observation_data because the source conclusion contains the real variable a in multiple coupled operands. The unresolved registration is tracked at https://github.com/the-omega-institute/trureturing/issues/30238; no declared_validated certificate is claimed.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.localFactorConstant`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.local_factor_lower_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.normalizedLocalFactor`
