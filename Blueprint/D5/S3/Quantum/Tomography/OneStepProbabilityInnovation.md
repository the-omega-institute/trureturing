# One-Step Probability Innovation

## Abstract

One complementary context removes exactly its centered probability energy.

**Theorem 1.1 (One context gives the exact probability innovation).**

$$\operatorname{residualMass}(S, \operatorname{densityCoordinate}(\rho)) - \operatorname{residualMass}(Snext, \operatorname{densityCoordinate}(\rho)) = \sum_{j} {\operatorname{contextProbability}(\rho, B, j)-\frac{1}{d}}^{2} \land \\\operatorname{orthogonal}(S) = \operatorname{centeredContextPlane}(B) + \operatorname{orthogonal}(Snext) \land \\\operatorname{centeredContextPlane}(B) \perp \operatorname{orthogonal}(Snext).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/OneStepProbabilityInnovation.one_step_probability_innovation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a density matrix and Xrho its canonical centered coordinate on the real trace-zero Hermitian carrier. Let S be the visible subspace before adding a complete rank-one context and Snext the visible subspace afterward.

The added context plane is constructed as the real span of its centered rank-one projectors, and each displayed probability is constructed by the Born trace rule. Assume S is contained in Snext, the new directions are exactly that centered context plane, and its projection energy is the sum of centered probability squares.

Then the old residual mass minus the new residual mass is exactly that probability sum. Public companion clauses state that the old residual space is the sum of the context plane and the new residual, and that these two summands are orthogonal.

The proof applies the repository's innovation-energy recurrence and Mathlib's exact nested-subspace orthogonal splitting theorem. Repository and pinned-library searches found no existing theorem combining all three clauses on the canonical quantum carrier.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/OneStepProbabilityInnovation.one_step_probability_innovation`
- Dependency: [D5/S3/Observer/Tomography/InnovationEnergyRecurrence](../../Observer/Tomography/InnovationEnergyRecurrence.md)
- Dependency: [D5/S3/Quantum/Tomography/RankOneContextCommutator](RankOneContextCommutator.md)
- Dependency: [D5/S3/Quantum/Tomography/ResidualControlsNaturality](ResidualControlsNaturality.md)
