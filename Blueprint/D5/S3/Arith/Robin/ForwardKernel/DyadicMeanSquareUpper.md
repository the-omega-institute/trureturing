# Dyadic mean-square upper bound

## Abstract

A uniform short-interval variance bound controls the dyadic mean square of the complete forward response.

Write E(x)=psi(x)-x, H(x)=x^(4/5), and D(x,theta)=E((1+theta)*x)-E(x), with the complete Chebyshev psi. Assume constants A>0 and Y>=2 such that, for every X>=Y and 0<theta<=1, the integral of D(x,theta)^2 over [X,2X] is at most A*theta*X^2*log(2/theta)^2. This is the explicit ShortIntervalMeanSquareBound hypothesis; no separate Riemann hypothesis is used.

**Definition 1.1 (Hypothesis (489.2)).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.CumulativeVarianceBandAsymptotic`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.CumulativeVarianceBandAsymptotic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hypothesis (489.2) is the uniform cumulative variance hypothesis for the complete Chebyshev error E(x)=psi(x)-x. It is an assumption: this definition asserts no proof of the variance asymptotic and includes neither a Riemann hypothesis assumption nor a separate regularity condition.

**Theorem 1.2 (Regularity of the Chebyshev error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function psi(x)-x is measurable and bounded in absolute value on every closed finite interval. Measurability comes from the measurability of the complete Chebyshev error; monotonicity and nonnegativity of psi give the compact bound.

**Theorem 1.3 (The dyadic upper estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.forward_kernel_dyadic_mean_square_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.forward_kernel_dyadic_mean_square_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist C>0 and X0>=3 such that, for every X>=X0, the integral of forwardResponse(x)^2/x over [X,2X] is at most C*X^(1/5)*log(X)^2.

The substitution u=theta*x expresses the response as sqrt(x)*x/H(x)^2 times the integral of D(x,theta) multiplied by w((1+theta)*x)/w(x), for 0<=theta<=H(x)/x. Positivity and monotonicity of w bound this ratio between zero and one. Cauchy–Schwarz therefore bounds the squared response divided by x by x/H(x)^3 times the integral of D(x,theta)^2. For x in [X,2X], enlarge the theta interval to [0,a], where a=X^(-1/5), and bound x/H(x)^3 by X^(-7/5). Bounded measurable increments justify Fubini on this rectangle. For X>=16^5, the function theta*log(2/theta)^2 is increasing up to a<=1/16. The assumed variance estimate then bounds the double integral by A*X^2*a^2*log(2/a)^2. Finally log(2/a)<=2*log(X), giving C=4*A and X0=max(Y,16^5).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.CumulativeVarianceBandAsymptotic`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.forward_kernel_dyadic_mean_square_upper`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MellinConvergence](MellinConvergence.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
