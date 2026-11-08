# Uniform first moments with continuous weights

## Abstract

For every continuous real weight on [1,2], the weighted first normalized moment tends to zero uniformly over s in [0,1], under the variance asymptotic on a band containing theta. The second absolute moment bound controls the approximation error, and uniform interval cancellation supplies the step-weight limit.

**Theorem 1.1 (Reciprocal power-logarithmic weights).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.logarithmic_weight_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.logarithmic_weight_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative p and q, the reciprocal of x^p log(x)^q is continuously differentiable, nonnegative and decreasing on x>1. Increasing the position increases both positive factors of its denominator.

**Theorem 1.2 (Uniform first primitive cancellation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_interval_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_interval_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a locally bounded Borel function whose cumulative variance has the stated uniform asymptotic on an exponent band containing theta, the integral of D_(s*x^theta)(x) on any subinterval of [X,2X], divided by X*sqrt(X^theta*log(X)), tends to zero uniformly over s in [0,1] and both endpoints. An intermediate exponent nu between theta and the upper band endpoint gives two negative powers after normalization of the moving primitive estimate.

**Theorem 1.3 (Cancellation with a decreasing logarithmic weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.logarithmic_weight_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.logarithmic_weight_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integrable family with uniform interval cancellation relative to X^p log(X)^q, where p and q are nonnegative, multiplication by the reciprocal power-logarithmic weight gives uniform unscaled interval cancellation. Integration by parts bounds each weighted integral by twice the primitive bound times the weight at X.

**Theorem 1.4 (Normalized first moments on subintervals).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_weighted_interval_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_weighted_interval_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the variance band asymptotic, the integral of B_theta(s,x)/x tends to zero uniformly over s in [0,1] and all subintervals of [X,2X]. This is the first moving increment multiplied by x^(-1-theta/2) log(x)^(-1/2).

**Theorem 1.5 (Integrability of normalized increment powers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.dyadicB_power_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.dyadicB_power_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural power of the normalized moving increment is integrable under logarithmic dyadic probability when X>1 and theta is nonnegative. The same power divided by position is interval integrable on [X,2X]. Local boundedness supplies integrable raw powers and the normalizing factor is continuous on this interval.

**Theorem 1.6 (Continuous dyadic weights).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.continuous_dyadic_weight_lifting`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.continuous_dyadic_weight_lifting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An interval integrable family with bounded absolute logarithmic mass and uniform cancellation on all dyadic subintervals has vanishing integrals against every continuous function of x/X under dyadic probability. The change of variables x=X*u reduces this to continuous weight approximation on [1,2].

**Theorem 1.7 (Uniform first moments with continuous weights).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_moment_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_moment_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every continuous real weight on [1,2], the weighted first normalized moment tends to zero uniformly over s in [0,1], under the variance asymptotic on a band containing theta. The second absolute moment bound controls the approximation error, and uniform interval cancellation supplies the step-weight limit.

**Theorem 1.8 (The first-moment interface).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_moment_interface`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_moment_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A locally bounded Borel function with the variance asymptotic on a band containing theta satisfies the first-moment interface with zero kernel. Cauchy–Schwarz bounds each first absolute normalized moment by the square root of the uniform second-moment bound. Choosing the continuous weight u to the power (1-theta)/2 in the uniform weighted limit supplies the mixed first-moment limit.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.continuous_dyadic_weight_lifting`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.dyadicB_power_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_interval_cancellation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_moment_interface`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_moment_uniform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.first_weighted_interval_cancellation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.logarithmic_weight_cancellation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.logarithmic_weight_regular`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean](FourthMomentMean.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs](MacroscopicVarianceDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightApproximation](MacroscopicWeightApproximation.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds](MomentInterfaceBounds.md)
