# Logarithmic exponential derivative chain

## Abstract

The logarithm of one minus a negative exponential is smooth on the positive half-line and has a strictly positive third derivative.

**Theorem 1.1 (Three derivatives on the positive half-line).**

$$\operatorname{ContDiffOn}\left(\operatorname{Real}\left(\right), 3, f, \operatorname{Ioi}\left(0\right)\right) \land (\forall x: \operatorname{Real}\left(\right), 0 < x \implies (\operatorname{deriv}\left(f, x\right) = \frac{1}{(\operatorname{exp}\left(x\right)-1)} \land \operatorname{iteratedDeriv}\left(2, f, x\right) = -\frac{\operatorname{exp}\left(x\right)}{(\operatorname{exp}\left(x\right)-1)^{2}} \land \operatorname{iteratedDeriv}\left(3, f, x\right) = \frac{\operatorname{exp}\left(x\right)(\operatorname{exp}\left(x\right)+1)}{(\operatorname{exp}\left(x\right)-1)^{3}} \land 0 < \operatorname{iteratedDeriv}\left(3, f, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives.log_one_sub_exp_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here f(t) is log(1-exp(-t)). For t greater than zero the logarithm's argument is positive. Differentiation on this open set gives the three displayed rational expressions. The numerator and denominator in the third expression are strictly positive. Smoothness is asserted on the positive half-line.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives.log_one_sub_exp_derivatives`
