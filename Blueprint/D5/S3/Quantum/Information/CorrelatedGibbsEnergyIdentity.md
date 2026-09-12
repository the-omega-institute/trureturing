# Energy and Information with Initial Correlations

## Abstract

Initially correlated states with thermal marginals obey an exact energy-information balance.

A and B are arbitrary finite nonempty subsystem index types. HA and HB are Hermitian physical Hamiltonians, and betaA and betaB are real inverse temperatures. thermalState(H,beta) is the existing Gibbs state exp(-beta H)/Tr(exp(-beta H)); E(H,rho) denotes meanEnergy(H,rho) = Re Tr(H rho). S is von Neumann entropy and D is quantum relative entropy, with natural logarithms. rhoA and rhoB are the actual partial traces marginalRight(rho) and marginalLeft(rho). The primed joint state is U rho U*, with U a joint unitary, and its primed marginals are obtained by the same partial traces.

**Theorem 1.1 (The local thermal identity).**

$$\forall H, beta, sigma, \operatorname{D}\left(sigma, gamma\right) = beta \cdot (\operatorname{E}\left(H, sigma\right) - \operatorname{E}\left(H, gamma\right)) - (\operatorname{S}\left(sigma\right) - \operatorname{S}\left(gamma\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.gibbs_relative_entropy_energy_difference` (`✓ std3`). ∎

*Citation.* Kaonan Micadei, John P. S. Peterson, Alexandre M. Souza, Roberto S. Sarthour, Ivan S. Oliveira, Gabriel T. Landi, Tiago B. Batalhão, Roberto M. Serra, Eric Lutz (2019). *Reversing the direction of heat flow using quantum correlations*. URL: <https://doi.org/10.1038/s41467-019-10333-7>.

*Commentary.*

For every initial density equal to gamma = thermalState(H,beta) and every final density sigma, the Gibbs variational identity at sigma and gamma has the same log partition function. Subtraction cancels it, and D(gamma,gamma) vanishes. The final state may be singular and need not commute with H.

**Lemma 1.2 (Joint entropy is conserved).**

$$\forall \rho, U, \operatorname{S}\left(\operatorname{unitaryConjugateState}\left(U, \rho\right)\right) = \operatorname{S}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.von_neumann_entropy_unitary` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For every density state and every unitary U, the existing entropy-production identity applied at U and at the identity matrix yields the same pinching relative entropy. Subtracting those equalities gives entropy conservation, including singular states. This argument uses the public entropy theorem.

**Theorem 1.3 (Marginal entropy changes measure correlation changes).**

$$\forall \rho, U, DeltaSA + DeltaSB = \operatorname{I}\left(rhoPrime\right) - \operatorname{I}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.marginal_entropy_change_eq_mutual_information_change` (`✓ std3`). ∎

*Citation.* Kaonan Micadei, John P. S. Peterson, Alexandre M. Souza, Roberto S. Sarthour, Ivan S. Oliveira, Gabriel T. Landi, Tiago B. Batalhão, Roberto M. Serra, Eric Lutz (2019). *Reversing the direction of heat flow using quantum correlations*. URL: <https://doi.org/10.1038/s41467-019-10333-7>.

*Commentary.*

For every joint density and joint unitary, I(rho) = S(rhoA) + S(rhoB) - S(rho). Subtracting initial from final mutual information cancels total entropy. Delta always means final minus initial; the initial correlation term remains.

**Theorem 1.4 (Energy-information identity with correlated initial states).**

$$\forall \rho, U, rhoA = gammaA \land rhoB = gammaB \implies betaA \cdot DeltaEA + betaB \cdot DeltaEB = \operatorname{D}\left(rhoAPrime, gammaA\right) + \operatorname{D}\left(rhoBPrime, gammaB\right) + \operatorname{I}\left(rhoPrime\right) - \operatorname{I}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.energy_information_identity` (`✓ std3`). ∎

*Citation.* Kaonan Micadei, John P. S. Peterson, Alexandre M. Souza, Roberto S. Sarthour, Ivan S. Oliveira, Gabriel T. Landi, Tiago B. Batalhão, Roberto M. Serra, Eric Lutz (2019). *Reversing the direction of heat flow using quantum correlations*. URL: <https://doi.org/10.1038/s41467-019-10333-7>.

*Commentary.*

Assume exactly rhoA = thermalState(HA,betaA) and rhoB = thermalState(HB,betaB). The initial joint state can have correlations. Add the two local thermal identities and substitute the marginal entropy relation. No energy conservation assumption is needed for this weighted identity.

## References

- Truth anchor: `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.energy_information_identity`
- Truth anchor: `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.gibbs_relative_entropy_energy_difference`
- Truth anchor: `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.marginal_entropy_change_eq_mutual_information_change`
- Truth anchor: `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.von_neumann_entropy_unitary`
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](../Divergence/GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
