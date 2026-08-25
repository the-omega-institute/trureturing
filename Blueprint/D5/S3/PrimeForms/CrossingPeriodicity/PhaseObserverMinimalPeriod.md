# Minimal Period of the Phase Observer

## Abstract

The named winding-phase observer has least positive translation period m divided by gcd(m,2), with the six-step modulus-twelve case.

**Definition 1.1 (The phase observer modulo a natural modulus).**

$$q_{m}(A)=[\operatorname{Psi}(A)]_{m}.$$

*Formalization.* `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phaseObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source symbol Psi is the existing windingPhase. Since that phase is rational, reduction modulo the natural m is represented by the existing rational additive circle of period m.

**Definition 1.2 (The closed-form phase period).**

$$T(m)=\frac{m}{\operatorname{gcd}(m, 2)}.$$

*Formalization.* `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phasePeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The period function is defined on natural moduli by dividing m by its greatest common divisor with the translation step two.

**Theorem 1.3 (The phase period is the least positive return time).**

$$\begin{aligned}\forall m\in \mathbb{N}, 0<m \Rightarrow \operatorname{ord}_{m}({-2})=T(m) \land 0<T(m)\\T(m)\cdot{-2}=0, \forall k, 0<k<T(m) \Rightarrow k\cdot{-2}\neq0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phase_period_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive m, Mathlib's exact additive-order formula for two in ZMod m gives T(m). Its minimal-order characterization proves both return and exclusion of every smaller positive step count.

**Theorem 1.4 (The additive-circle period agrees with the closed form).**

$$0<m \Rightarrow \operatorname{ord}_{\operatorname{AddCircle}(m)}(-2)=T(m) \land 0<T(m).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phase_period_addCircle_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported observer evolves by translation by minus two on AddCircle m. Mathlib's gcd-times-order identity proves that this step has the same order T(m), so the ZMod calculation and the existing model agree.

**Theorem 1.5 (A positive modulus is necessary).**

$$\neg{0<T(0) \land \operatorname{ord}_{0}(-2)=T(0)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.positive_modulus_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At m=0 the closed form is zero. The additive-order convention also reports zero for the infinite-order translation in ZMod 0, but zero cannot be a least positive period, so positivity is a necessary hypothesis.

**Theorem 1.6 (The modulus-twelve period is six).**

$$\begin{aligned}12=4\cdot3,\\T(4)=2, T(3)=3,\\T(12)=\operatorname{lcm}(2, 3)=6.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phase_period_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed calculation records the source's coprime factors four and three, their periods two and three, and the resulting least common multiple six. It checks the CRT path numerically rather than proving a general CRT theorem for arbitrary moduli.

## References

- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phaseObserver`
- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phasePeriod`
- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phase_period_addCircle_eq`
- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phase_period_eq`
- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.phase_period_twelve`
- Truth anchor: `D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.positive_modulus_is_necessary`
- Dependency: [D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverTranslation](PhaseObserverTranslation.md)
- Dependency: [D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod](SandwichPhasePeriod.md)
