# Actual integer power generator

## Abstract

The actual compensated generator has a scaled comparison with the signed Mellin integral.

**Definition 1.1 (Shifted inverse power on the integers).**

$$p_{\beta}(z)=\left(2+\left\lvert z\right\rvert\right)^{-\beta}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.powerProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position z is an integer, read as a real inside the absolute value; beta is real.

**Definition 1.2 (Compensated generator with the actual weights).**

$$\mathcal{D}_{\kappa}\left(u,z\right)=\sum_{i=0}^{\infty}\kappa_{i}\cdot \left(u(z+\left(i+1\right))+u(z-\left(i+1\right))-2\cdot u(z)\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.actualGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function u maps integers to reals. The weight at index i is the occupation kernel's actual weight for jump size i+1, including its singleton term. The series is the real infinite sum.

**Theorem 1.3 (Uniform signed discrepancy and lower bound).**

$$\begin{gathered}\exists A,C\in \mathbb{R}, 0<A \land 0\le C \land\\{}(\forall \beta\in \mathbb{R}, n\in \mathbb{N},\\{}\frac{1}{2}\le\beta\le\frac{3}{4} \land 4^{20}\le n\longrightarrow\\{}\left\lvert n^{\beta+\frac{1}{2}}\cdot \mathcal{D}_{\kappa}\left(p_{\beta},n\right)-A\cdot J(\beta)\right\rvert\le C\cdot n^{-\frac{1}{80}} \land\\{}A\cdot c\cdot \left(\beta-\frac{1}{2}\right)-C\cdot n^{-\frac{1}{80}}\le n^{\beta+\frac{1}{2}}\cdot \mathcal{D}_{\kappa}\left(p_{\beta},n\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.actual_generator_power_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same two constants work for both inequalities, for every allowed exponent and mesh size. All powers of n are taken in the reals and the generator is evaluated at n as an integer. Here J is the signed whole-line Mellin integral and c is its fixed positive Kelvin coefficient.

The half-line integral separates into two affine rays of the signed whole-line kernel. After normalizing the mesh, the leading power weight gives the integral term and the summable weight replacement gives an error. The Kelvin gap yields the one-sided bound.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.actualGenerator`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.actual_generator_power_comparison`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.powerProfile`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedComparison](OccupiedComparison.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement](OccupiedKernelWeightReplacement.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinFloors](OccupiedMellinFloors.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin](OccupiedMellinKelvin.md)
