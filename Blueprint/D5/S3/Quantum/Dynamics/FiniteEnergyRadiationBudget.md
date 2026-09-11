# Finite energy radiation budget

## Abstract

A nonnegative energy reservoir bounds integrated radiation and constant-power duration.

Let E and P be real functions of real time, with initial time u0. Assume E has derivative -P(u) for every u > u0, E is continuous from the right at u0, and E(u) and P(u) are nonnegative for every u >= u0. These hypotheses describe energy loss through radiation without an incoming source.

**Theorem 1.1 (Total radiated energy).**

$$\operatorname{IntegrableOn}\left(P, \operatorname{Ioi}\left(u_{0}\right)\right) \land \int_{u_{0}}^{\infty} \operatorname{P}\left(u\right) du \le \operatorname{E}\left(u_{0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget.finite_energy_radiation_budget` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Monotone primitives and the fundamental theorem of calculus on a ray*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean>.

*Commentary.*

The energy is antitone on the closed ray. Extending it by E(max(u0,u)) gives an antitone function on the whole real line with lower bound zero. Its infimum L is nonnegative, and E(u) tends to L as u tends to infinity.

A derivative of one sign whose primitive has a finite limit is integrable on the ray. The fundamental theorem of calculus then gives the total radiated energy as E(u0)-L, at most E(u0). Right continuity at the initial time identifies the boundary term with E(u0).

**Theorem 1.2 (Duration of constant positive power).**

$$\Delta \le \frac{\operatorname{E}\left(u_{0}\right)}{P_{0}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget.constant_power_duration_le` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Monotone primitives and the fundamental theorem of calculus on a ray*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean>.

*Commentary.*

Under the same assumptions, let Delta be nonnegative and P0 strictly positive. Suppose P(u)=P0 on [u0,u0+Delta]. The radiation integral over this interval equals Delta times P0. Nonnegativity of P bounds it by the total radiation, which is at most E(u0). Division by P0 gives the duration bound.

Thus a fixed positive power cannot persist for arbitrarily long initial intervals when the initial energy is finite.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget.constant_power_duration_le`
- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget.finite_energy_radiation_budget`
