# Critical occupation-kernel coefficient estimate

## Abstract

The actual critical occupation kernel has a positive leading coefficient and a uniform smaller-order remainder.

Let U(m) be the set of permutations of size m avoiding 2413 and 3142, and let rho=(sqrt(2)-1)^2. At jump length m>=1 the weight kernelWeight(m-1) is rho^m times the cardinality of U(m), with an additional rho/2 at length one only.

**Theorem 1.1 (Positive leading term with uniform remainder for lengths at least two).**

$$\exists C\in\mathbb{R}, C>0 \land (\forall m\in\mathbb{N}, 2\le m\Rightarrow \left\Vert\operatorname{kernelWeight}\left(m-1\right)-\frac{C}{m\sqrt{m}}\right\Vert\le\frac{\frac{21}{16}}{m^2\sqrt{m}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedKernelCoefficient.actual_kernel_weight_strict_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The length restriction is a natural-number inequality; powers and square roots in the denominators are real. One constant C works for every admissible length, and the singleton correction is not part of the estimate.

The actual cardinality formula makes the normalized generating function quadratic. Its discriminant factors into formal series with linear factors at the critical and rescaled arguments. The constant-one root identifies the coefficients as a convolution of signed central-binomial coefficients with one factor geometrically damped by powers of rho squared. An adjacent-ratio estimate controls the normalized central-binomial profile. Splitting the convolution at half the jump length then bounds both the local coefficient error and the damped tail with the stated uniform constant.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedKernelCoefficient.actual_kernel_weight_strict_remainder`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCountRatios](ActualCountRatios.md)
