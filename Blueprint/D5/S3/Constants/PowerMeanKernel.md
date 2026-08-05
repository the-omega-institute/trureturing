# Power Mean Kernels

## Abstract

Five discrete power means define the rationalizable symmetric metric kernels.

**Theorem 1.1 (The half-power mean is an average).**

$$M_\frac{1}{2}{a,b}=\frac{M_0{a,b}+M_1{a,b}}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/PowerMeanKernel.meanHalf_eq_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative a and b, expanding the square in the half-power mean and using sqrt(a b) = sqrt(a) sqrt(b) gives the identity.

The same Lean module defines the parameters -1, -1/2, 0, 1/2, and 1, together with the symmetric metric-kernel conversion k(t) = 2 / M(1+t, 1-t). It also proves the harmonic and arithmetic symmetric-input reductions. Exact integral evaluations and the completeness of the genus-zero parameter list are outside this algebraic theorem's scope.

## References

- Truth anchor: `D5/S3/Constants/PowerMeanKernel.meanHalf_eq_average`
