# The Lower Mechanical Complexity Characterization

## Abstract

Characterize irrational lower mechanical slopes simultaneously by exact factor complexity and failure of eventual periodicity.

Fix a real slope alpha in the half-open interval from zero to one and an arbitrary real intercept rho. Factors begin at natural indices, and eventual periodicity uses the repository's one-sided natural-tail convention.

**Theorem 1.1 (A positive period bounds every factor count).**

$$\forall p\in\mathbb{N}, 0 < p \land \operatorname{Periodic}(w_{\alpha,\rho},p) \Rightarrow \forall n\in\mathbb{N}, \operatorname{card}(FactorSet(\alpha,\rho,n)) \leq p$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lower_mechanical_factor_set_card_le_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Periodicity is lifted pointwise through each finite factor. Reducing every start modulo p shows that all occurring factors are represented among the first p starts, and the cardinality of an image cannot exceed its domain.

**Theorem 1.2 (Exact n plus one complexity is equivalent to irrationality).**

$$[\forall n\in\mathbb{N}, \operatorname{card}(FactorSet(\alpha,\rho,n)) = n + 1] \iff \operatorname{Irrational}(\alpha)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lower_mechanical_factor_complexity_iff_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward implication excludes every rational slope. Its reduced denominator p is a positive period, so the factor count at length p is at most p rather than p plus one.

The reverse implication is the frozen irrational lower-mechanical factor-complexity theorem, applied at every length.

**Theorem 1.3 (Complexity, irrationality, and aperiodicity coincide).**

$$\forall \alpha,\rho\in\mathbb{R}, 0 \leq \alpha < 1, ([\forall n\in\mathbb{N}, \operatorname{card}(FactorSet(\alpha,\rho,n)) = n + 1] \iff \operatorname{Irrational}(\alpha)) \land (\operatorname{Irrational}(\alpha) \iff \neg\operatorname{EventuallyPeriodic}(w_{\alpha,\rho}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lower_mechanical_factor_complexity_iff_irrational_iff_not_eventuallyPeriodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first equivalence is the new rational-factor exclusion. The second is obtained by negating the frozen equivalence between rationality and eventual periodicity. Together they state the requested three-way classification without changing either frozen convention.

## References

- Truth anchor: `D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lower_mechanical_factor_complexity_iff_irrational`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lower_mechanical_factor_complexity_iff_irrational_iff_not_eventuallyPeriodic`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lower_mechanical_factor_set_card_le_period`
- Dependency: [D5/S1/Words/Mechanical/MechanicalFactorComplexity](../Mechanical/MechanicalFactorComplexity.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalPeriodicity](../Mechanical/MechanicalPeriodicity.md)
