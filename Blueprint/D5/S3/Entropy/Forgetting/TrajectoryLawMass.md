# Trajectory Law Mass

## Abstract

Deterministic trajectory laws conserve total mass and preserve nonnegativity.

The frozen module Entropy/Forgetting/TrajectoryEntropyTelescoping defines trajectoryLaw update initial by recursion on time: the law at time 0 is initial, and the law at time k + 1 is the pushforward of the law at time k along update. Its type is fixed to the reals, so both statements below are real-valued.

Beyond the Fintype instance on Y, which the finite sums need, the mass identity carries no hypothesis. It is stated as an equality between the total mass at time k and the total mass of initial, so it holds for an arbitrary real weighting: neither nonnegativity nor normalisation of initial is used, and nothing is assumed about update.

The induction step is Mathlib's Finset.sum_fiberwise, restated in the indicator-weighted form that pushforward is written in. The mathematical content of the step is Mathlib's; this module supplies the statement about trajectoryLaw, which Mathlib cannot state because trajectoryLaw is a definition of this development.

Two modules each carry private copies of both facts about trajectoryLaw: Entropy/Forgetting/TrajectoryEntropyTelescoping and Entropy/Forgetting/DeterministicEntropyStep, four private declarations under these names. Each private mass copy assumes that initial sums to one and concludes that the law sums to one. Reading those proofs, the hypothesis enters only through the base case; the successor branch establishes that the mass at time k+1 equals the mass at time k without using it, and then closes with the induction hypothesis. That is why the mass statement here drops the hypothesis and names the conserved quantity instead. This count is of declarations about trajectoryLaw under those two names; it is not a count of every place the one-step fact appears.

Both modules are frozen, and so is TrajectoryEntropyTelescoping, which supplies the definition. Being frozen, neither can import this module, and this change removes none of the four private copies. This module has zero consumers today.

**Theorem 1.1 (Deterministic trajectories conserve total mass).**

$$\begin{aligned}\forall Y: Type, [Fintype\left(Y\right)],\\\forall update: Y \to Y, initial: Y \to R,\\\forall k: N,\\\sum_{y} trajectoryLaw\left(update initial k y\right) = \sum_{y} initial\left(y\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/TrajectoryLawMass.trajectoryLaw_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state type Y carries a Fintype instance and is otherwise arbitrary, update is an arbitrary function, initial is an arbitrary real weighting, and the time k is an arbitrary natural number. Beyond that instance there are no hypotheses.

**Theorem 1.2 (Deterministic trajectories preserve nonnegativity).**

$$\begin{aligned}\forall Y: Type, [Fintype\left(Y\right)],\\\forall update: Y \to Y, initial: Y \to R,\\(\forall y, 0 \le initial\left(y\right)) \implies\\\forall k y, 0 \le trajectoryLaw\left(update initial k y\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/TrajectoryLawMass.trajectoryLaw_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Beyond the Fintype instance on Y, pointwise nonnegativity of initial is the only hypothesis. No normalisation is required, and update is arbitrary.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/TrajectoryLawMass.trajectoryLaw_nonneg`
- Truth anchor: `D5/S3/Entropy/Forgetting/TrajectoryLawMass.trajectoryLaw_sum_eq`
- Dependency: [D5/S3/Entropy/Forgetting/TrajectoryEntropyTelescoping](TrajectoryEntropyTelescoping.md)
