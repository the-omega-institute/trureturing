# Uniform Recurrence of Irrational Lower Mechanical Words

## Abstract

Prove uniform recurrence for lower mechanical words at every irrational slope.

Fix an irrational real slope alpha in the half-open interval from zero to one, an arbitrary real intercept rho, and a finite factor that occurs at a natural starting index.

**Theorem 1.1 (Every occurring factor returns within one uniform window bound).**

$$\forall \alpha, \rho\in \mathbb{R}, 0 \leq \alpha < 1 \land \operatorname{Irrational}(\alpha) \Rightarrow \forall n\in \mathbb{N}, \forall w\in FactorSet(\alpha, \rho, n), \ \exists R\in \mathbb{N}, \forall i\in \mathbb{N}, \ \exists j\in \mathbb{N}, i \leq j \land j + n \leq i + R \land w = \operatorname{lowerMechanicalFactor}(\alpha, \rho, n, j)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalUniformRecurrence.lower_mechanical_factor_uniformly_recurrent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a witnessing start, choose a real phase interval immediately to the right and stop before both the next finite coding breakpoint and one. The lower word uses a half-open threshold, so every phase in this right-sided interval has the same prefix counts and therefore the same factor.

The interval maps to an open arc of the additive circle without crossing the quotient seam. Irrational rotation makes the forward orbit from every circle point meet that arc. Compactness supplies a finite subcover by inverse translates, and the largest translate index bounds every waiting time.

For an arbitrary intercept, equality on the circle is returned to the canonical real phase by the unique representative in the half-open interval from zero to one. Adding the factor length to the waiting-time bound places the entire returned factor inside the asserted window.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalUniformRecurrence.lower_mechanical_factor_uniformly_recurrent`
- Dependency: [D5/S1/Words/Mechanical/MechanicalFactorComplexity](MechanicalFactorComplexity.md)
