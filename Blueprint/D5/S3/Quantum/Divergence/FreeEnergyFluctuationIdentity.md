# Free energy and energy fluctuations

## Abstract

Derivatives of the free energy of a finite-dimensional Gibbs family are given by the mean energy and its fluctuation.

**Definition 1.1 (Parameterized partition function).**

$$\operatorname{Z}\left(nu\right) = \operatorname{partitionFunction}\left({-betanu} H\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.parameterizedPartitionFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scaling a fixed self-adjoint Hamiltonian by minus beta times the family parameter gives the partition function.

**Definition 1.2 (Free energy).**

$$\operatorname{F}\left(nu\right) = -\frac{1}{beta} \operatorname{log}\left(\operatorname{Z}\left(nu\right)\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.freeEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The free energy is minus the inverse beta times the logarithm of the partition function.

**Definition 1.3 (Equilibrium state).**

$$\operatorname{rho}\left(nu\right) = \operatorname{thermalState}\left(H, beta, nu\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.equilibriumState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equilibrium state is the existing thermal state at beta times the family parameter.

**Theorem 1.4 (First derivative).**

$$\operatorname{Fprime}\left(nu\right) = \operatorname{E}\left(nu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.free_energy_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the partition function derivative is minus beta times the partition function times the energy expectation, the free energy derivative equals the mean energy.

**Theorem 1.5 (Second derivative).**

$$\operatorname{Fsecond}\left(nu\right) = -beta \operatorname{Var}\left(nu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.free_energy_second_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the mean energy derivative is minus beta times the energy variance, the second free energy derivative is minus beta times that variance.

**Theorem 1.6 (Concavity).**

$$\operatorname{Fsecond}\left(nu\right) \le 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.free_energy_concave_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive beta, the fluctuation formula makes the second derivative nonpositive.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.equilibriumState`
- Truth anchor: `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.freeEnergy`
- Truth anchor: `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.free_energy_concave_at`
- Truth anchor: `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.free_energy_deriv`
- Truth anchor: `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.free_energy_second_deriv`
- Truth anchor: `D5/S3/Quantum/Divergence/FreeEnergyFluctuationIdentity.parameterizedPartitionFunction`
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
- Dependency: [D5/S3/Quantum/Information/CovarianceSumBound](../Information/CovarianceSumBound.md)
