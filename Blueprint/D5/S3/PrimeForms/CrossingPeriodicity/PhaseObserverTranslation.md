# Phase Observer Translation

## Abstract

The winding-phase observer carries the admissible crossing sandwich to the explicit translation by minus two on every rational additive circle.

**Theorem 1.1 (The phase observer descends to translation).**

$$\begin{aligned}\forall m\in \mathbb{Q}, q_{m}(A)=[Psi(A)]_{m}\\T_{m}: \operatorname{AddCircle}\left(m\right) \to \operatorname{AddCircle}\left(m\right), T_{m}(z)=z-2\\q_{m} \circ sigma=T_{m} \circ q_{m}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverTranslation.phase_observer_descends_to_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source state space consists of positive matrices satisfying the existing admissibility predicate. Its update is the existing crossing sandwich, which preserves that predicate.

For an arbitrary rational modulus m, the observer sends a matrix to its winding phase in the additive quotient by m. The target map is constructed explicitly as subtraction by two.

The exact single-step phase law proves that observing after the source update is the same as translating after observation. Thus the phase dynamics descends to the displayed translation.

## References

- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverTranslation.phase_observer_descends_to_translation`
- Dependency: [D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod](SandwichPhasePeriod.md)
