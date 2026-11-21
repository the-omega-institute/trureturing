# Maximum mass of globally fixed seeds

## Abstract

Sharp mass of globally fixed seeds in equivariant probability calibration.

**Theorem 1.1 (The least row mass on stabilizer-fixed outputs is attained).**

$$\forall P, \operatorname{CovariantProbabilityKernel}\left(P\right) \Rightarrow \exists x, (\forall y, \operatorname{RowFixedMass}\left(P, x\right) \le \operatorname{RowFixedMass}\left(P, y\right)) \land \operatorname{UniversalFixedMassBound}\left(P, \operatorname{RowFixedMass}\left(P, x\right)\right) \land \operatorname{PositiveInvariantAttainment}\left(P, \operatorname{RowFixedMass}\left(P, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FixedKernelMass.maximal_fixed_seed_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts on a nonempty finite input set X and a finite output set Y. The nonnegative kernel P has row sums one and is covariant. RowFixedMass sums a row over the outputs fixed by every group element fixing that input. SeedFixedMass sums the weights of all seeds fixed by the whole group.

The same minimizing row bounds the fixed mass of every finite calibration with nonnegative weights and an equivariant readout. There is an attaining calibration with strictly positive weights summing to one, invariant under the group action, with all row marginals equal to P.

For attainment, take the least row mass in proportion from each row's stabilizer-fixed output set. Sample the normalized fixed part at one representative per input orbit and transport the outputs along the orbit. The residual kernel is calibrated by independent row draws. Mix the two parts using their total masses and omit the part of weight zero at each endpoint.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FixedKernelMass.maximal_fixed_seed_mass`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers](FiniteKernelStabilizers.md)
