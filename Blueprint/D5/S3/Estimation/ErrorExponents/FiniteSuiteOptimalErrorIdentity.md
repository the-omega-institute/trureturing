# Finite-Suite Optimal Error Identity

## Abstract

Optimal equal-prior error is determined exactly by total variation, with explicit normalization and degeneracy audits.

**Theorem 1.1 (Optimal error equals half of one minus total variation).**

$$\begin{aligned}\forall p, q: Index \to \left(Outcome \to \mathbb{R}\right),\\{}\forall i, \sum_{a} \operatorname{eval}\left(p, i, a\right) = 1 \land \forall i, \sum_{a} \operatorname{eval}\left(q, i, a\right) = 1 \Rightarrow\\\operatorname{finiteSuiteOptimalError}\left(p, q\right) = \frac{1 - \operatorname{totalVariation}\left(\operatorname{windowLaw}\left(p\right), \operatorname{windowLaw}\left(q\right)\right)}{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.finite_suite_optimal_error_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum ranges over every decision event on the finite product outcome space. The attaining Le Cam event gives the upper direction, and the eventwise Le Cam inequality gives the lower direction.

Only coordinate normalization is required. The nonnegativity clauses from the private source proof do not enter either direction and are therefore omitted from the public statement.

**Theorem 1.2 (First normalization is necessary).**

$$Index = Outcome = Unit \Rightarrow \neg \operatorname{finiteSuiteOptimalError}\left((i, a) \mapsto 0, (i, a) \mapsto 1\right) = \frac{1 - \operatorname{totalVariation}\left(\operatorname{windowLaw}\left((i, a) \mapsto 0\right), \operatorname{windowLaw}\left((i, a) \mapsto 1\right)\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.p_normalization_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Unit indices and Unit outcomes, the zero first law and unit second law give optimal error zero but make the claimed right side one quarter.

**Theorem 1.3 (Second normalization is necessary).**

$$Index = Outcome = Unit \Rightarrow \neg \operatorname{finiteSuiteOptimalError}\left((i, a) \mapsto 1, (i, a) \mapsto 0\right) = \frac{1 - \operatorname{totalVariation}\left(\operatorname{windowLaw}\left((i, a) \mapsto 1\right), \operatorname{windowLaw}\left((i, a) \mapsto 0\right)\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.q_normalization_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Swapping the concrete zero and unit laws again gives optimal error zero and right side one quarter, so the second normalization is essential.

**Theorem 1.4 (An empty outcome cannot be normalized at a nonempty index).**

$$\forall p: Unit \to \left(Empty \to \mathbb{R}\right), \neg \forall i, \sum_{a} \operatorname{eval}\left(p, i, a\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.empty_outcome_normalization_is_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the concrete Unit index, a sum over Empty is zero. It therefore cannot satisfy the required unit-mass equation.

**Theorem 1.5 (The identity holds for an empty index).**

$$Index = Empty \Rightarrow \operatorname{finiteSuiteOptimalError}\left(p, q\right) = \frac{1 - \operatorname{totalVariation}\left(\operatorname{windowLaw}\left(p\right), \operatorname{windowLaw}\left(q\right)\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.empty_index_optimal_error_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With no coordinates, normalization is vacuous and both window laws are the same empty product. This remains valid for an empty outcome type.

**Theorem 1.6 (Equal laws have half error and zero total variation).**

$$\forall i, \sum_{a} \operatorname{eval}\left(p, i, a\right) = 1 \Rightarrow \operatorname{finiteSuiteOptimalError}\left(p, p\right) = \frac{1}{2} \land \operatorname{totalVariation}\left(\operatorname{windowLaw}\left(p\right), \operatorname{windowLaw}\left(p\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.equal_laws_optimal_error_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identical normalized coordinate laws induce identical product laws. Their total variation is zero and no equal-prior decision beats one half.

## References

- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.empty_index_optimal_error_eq`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.empty_outcome_normalization_is_impossible`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.equal_laws_optimal_error_eq`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.finite_suite_optimal_error_eq`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.p_normalization_is_necessary`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.q_normalization_is_necessary`
- Dependency: [D5/S3/Estimation/ErrorExponents/FiniteSuiteErrorSqueeze](FiniteSuiteErrorSqueeze.md)
