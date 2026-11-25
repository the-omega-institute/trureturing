# Truncated inverse-power mixture

## Abstract

Integrating the actual generator over a truncated interval of exponents preserves a positive tail contribution.

**Definition 1.1 (Finite exponent mixture).**

$$\tau(z)=\int_{0}^{\frac{1}{4}}p_{\frac{1}{2}+s}(z)\,ds$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture.truncatedProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position z is an integer. The integrand is the shifted inverse-power profile at exponent one half plus s.

**Theorem 1.2 (Interchange, closed form, and eventual gain).**

$$\begin{gathered}(\forall z\in \mathbb{Z},\\{}\mathcal{D}_{\kappa}\left(\tau,z\right)=\int_{0}^{\frac{1}{4}}\mathcal{D}_{\kappa}\left(p_{\frac{1}{2}+s},z\right)\,ds \land\\{}\tau(z)=\frac{1-X^{-\frac{1}{4}}}{\sqrt{X}\cdot\log X}) \land\\{}(\exists c\in \mathbb{R}, 0<c \land \operatorname{Eventually}_{n\to\infty}\left(\frac{c}{n\cdot \left(\log n\right)^{2}}\le \mathcal{D}_{\kappa}\left(\tau,n\right)\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture.truncated_profile_analysis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the closed form, X is two plus the absolute value of the real cast of z. The generator uses the actual occupation kernel weights. The eventual assertion is as n tends to infinity through the natural numbers, with the generator evaluated at n as an integer.

The exponent integral commutes with the generator because the sum of the integrals of the absolute terms is finite. For the lower estimate, the positive Kelvin gap supplies a first moment weighted by the exponent of minus s times log n. Integrating from zero to the reciprocal of log n gives an inverse-log-square gain; the algebraic error is smaller for sufficiently large n.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture.truncatedProfile`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture.truncated_profile_analysis`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator](OccupiedActualPowerGenerator.md)
