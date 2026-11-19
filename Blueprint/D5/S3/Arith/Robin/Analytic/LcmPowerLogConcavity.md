# A logarithmically concave power difference

## Abstract

Strict logarithmic concavity of consecutive real power differences.

**Definition 1.1 (The difference of consecutive powers).**

$$\forall kappa \in \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{powerDifference}\left(kappa, t\right) = (1 + t)^{kappa} - (t)^{kappa}$$

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.powerDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real kappa and t define C(kappa,t)=(1+t)^kappa-t^kappa. The powers are real powers. This is a total real-valued definition; the concavity conclusion below assumes kappa>1 and t>=0.

**Definition 1.2 (The logarithmic difference).**

$$\forall kappa \in \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{logPowerDifference}\left(kappa, t\right) = \operatorname{log}\left(\operatorname{powerDifference}\left(kappa, t\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.logPowerDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(kappa,t) is the total real logarithm of C(kappa,t). For kappa>1 and t>=0 the power difference is strictly positive, so this logarithm has its ordinary positive-argument interpretation.

**Theorem 1.3 (Positivity of the power difference).**

$$\forall kappa \in \mathbb{R},\; \forall t \in \mathbb{R},\; \left(1 < kappa \land 0 \le t\right) \Rightarrow (0 < \operatorname{powerDifference}\left(kappa, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.difference_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa>1 and t>=0, strict increase of positive real powers gives C(kappa,t)>0.

**Theorem 1.4 (The logarithmic derivative).**

$$\forall kappa \in \mathbb{R},\; \forall t \in \mathbb{R},\; \left(1 < kappa \land 0 < t\right) \Rightarrow (\operatorname{HasDerivAt}\left(\operatorname{logPowerDifference}\left(kappa\right), \frac{kappa \cdot \left((1 + t)^{kappa - 1} - (t)^{kappa - 1}\right)}{\operatorname{powerDifference}\left(kappa, t\right)}, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.log_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa>1 and t>0, B has the displayed derivative. The power difference is positive, so the logarithmic chain rule applies. This derivative also supplies the elasticity used to compare the F equation solutions.

**Theorem 1.5 (The exact curvature identity).**

$$\forall kappa \in \mathbb{R},\; \forall t \in \mathbb{R},\; 0 < t \Rightarrow ((\operatorname{deriv}\left(\operatorname{powerDifference}\left(kappa\right), t\right))^{2} - \operatorname{powerDifference}\left(kappa, t\right) \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{powerDifference}\left(kappa\right)\right), t\right) = kappa \cdot ((1 + t)^{kappa - 1} - (t)^{kappa - 1})^{2} + kappa \cdot \left(kappa - 1\right) \cdot (t \cdot \left(1 + t\right))^{kappa - 2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.powerDifference_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real kappa and every t>0 the displayed derivative identity holds. It follows from C'(t)=kappa*((1+t)^(kappa-1)-t^(kappa-1)) and C''(t)=kappa*(kappa-1)*((1+t)^(kappa-2)-t^(kappa-2)). Positivity of kappa-1 is needed only for the subsequent concavity conclusion.

**Theorem 1.6 (Strict concavity and the zero endpoint).**

$$\forall kappa \in \mathbb{R},\; 1 < kappa \Rightarrow (\operatorname{StrictConcaveOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), \operatorname{logPowerDifference}\left(kappa\right)\right) \land \left(\operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{Ici}\left(0\right), \operatorname{logPowerDifference}\left(kappa\right)\right) \land \operatorname{logPowerDifference}\left(kappa, 0\right) = 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.logPowerDifference_concavity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real kappa>1, B(kappa,.) is strictly concave on the open positive half-line and concave on the closed nonnegative half-line, and its value at zero is zero. No upper bound on kappa is assumed.

Write D(t)=(1+t)^(kappa-1)-t^(kappa-1). On t>0 the exact identity (C'(t))^2-C(t)*C''(t)=kappa*D(t)^2+kappa*(kappa-1)*(t*(1+t))^(kappa-2) has a strictly positive right-hand side. The quotient formula for the second derivative of log(C) therefore gives B''<0. Continuity at zero extends the concavity to the closed half-line, and C(kappa,0)=1 gives B(kappa,0)=0.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.difference_pos`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.logPowerDifference`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.logPowerDifference_concavity`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.log_derivative`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.powerDifference`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.powerDifference_curvature`
