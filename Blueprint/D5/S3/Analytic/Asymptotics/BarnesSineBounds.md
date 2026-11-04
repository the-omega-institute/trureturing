# Sine bounds for Barnes contours

## Abstract

Complex sine grows exponentially on every vertical line away from its real zeros.

**Theorem 1.1 (A sine lower bound).**

$$\forall x \in Real,\; \forall y \in Real,\; (\frac{\left|sin\left((\pi *x)\right)\right|}{2}*exp\left((\pi *\left|y\right|)\right)) \le \left\lVert sin\left((\pi *(x+(y*\operatorname{ComplexI})))\right) \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/BarnesSineBounds.barnesRes_sin_lower_line` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

Here pi is the circle constant, i is the imaginary unit, and real inputs in complex expressions are embedded in Complex. The square of the sine norm is sin(x)^2+sinh(y)^2; its cosh bound yields the displayed estimate.

**Theorem 1.2 (A bound uniform in the real coordinate).**

$$\forall x \in Real,\; \forall y \in Real,\; 1 \le \left|y\right| \Rightarrow (\frac{1}{4}*exp\left((\pi *\left|y\right|)\right)) \le \left\lVert sin\left((\pi *(x+(y*\operatorname{ComplexI})))\right) \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/BarnesSineBounds.barnesRes_sin_lower_far` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

For abs(y) at least one, the sinh term gives exp(pi*abs(y))/4 independently of x. The literal kernel horizontal-decay proof uses this bound uniformly on each finite strip.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/BarnesSineBounds.barnesRes_sin_lower_far`
- Truth anchor: `D5/S3/Analytic/Asymptotics/BarnesSineBounds.barnesRes_sin_lower_line`
