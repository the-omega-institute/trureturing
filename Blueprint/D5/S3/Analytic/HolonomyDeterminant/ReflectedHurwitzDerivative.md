# Reflected Hurwitz derivative at zero

## Abstract

Lerch's formula determines both reflected Hurwitz derivatives at zero.

**Theorem 1.1 (Lerch's formula on the open unit interval).**

$$\forall a \in \mathbb{R},\; \left(0 < a \land a < 1\right) \Rightarrow \left(\operatorname{zetaPrime}\left(0, a\right) = \operatorname{log}\left(\operatorname{Gamma}\left(a\right)\right) - \frac{\operatorname{log}\left(2 \times \pi\right)}{2} \land \operatorname{zetaPrime}\left(0, 1 - a\right) = \operatorname{log}\left(\operatorname{Gamma}\left(1 - a\right)\right) - \frac{\operatorname{log}\left(2 \times \pi\right)}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HolonomyDeterminant/ReflectedHurwitzDerivative.has_reflected_hurwitz_derivative_at_zero_formula` (`✓ std3`). ∎

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Hurwitz Zeta Function*. URL: <https://dlmf.nist.gov/25.11.E18>.

*Commentary.*

Let a be real with 0<a<1. The derivative is taken in the complex zeta argument. Subtract the Riemann partial sum from the Hurwitz partial sum and add (1-a)N to the power -s. The increments are interpolation remainders, bounded by 24 times N to the power -3/2 on the disk |s-1|<3/2. Uniform convergence and analytic continuation identify the limit with the zeta difference. Holomorphic derivative convergence and the Bohr-Mollerup limit give log Gamma. The Riemann derivative at zero supplies the constant. Applying the formula at 1-a gives the reflected sector, since 1-a and -a represent the same point of the additive circle.

## References

- Truth anchor: `D5/S3/Analytic/HolonomyDeterminant/ReflectedHurwitzDerivative.has_reflected_hurwitz_derivative_at_zero_formula`
- Dependency: [D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant](MasslessHolonomyDeterminant.md)
