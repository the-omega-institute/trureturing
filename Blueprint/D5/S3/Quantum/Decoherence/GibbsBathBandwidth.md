# Minimum Gibbs bath bandwidth

## Abstract

Sharp minimum energy range for finite Gibbs-bath preparation from a maximally mixed memory.

**Theorem 1.1 (Two-sided bounds on the retained marginal).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.marginal_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.marginal_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb, Michael J. Kastoryano and Michael M. Wolf (2011). *Hilbert’s projective metric in quantum information theory*. DOI: [10.1063/1.3615729](https://doi.org/10.1063/1.3615729). URL: <https://arxiv.org/abs/1102.5170v2>.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

Let the memory dimension be d, the bath dimension be b and the bath input be a Gibbs state with extreme probabilities τ_min and τ_max. The initial memory is maximally mixed. Unitary conjugation preserves the matrix order interval of the product input, and tracing out the bath gives (b/d)τ_min I ≤ ρ ≤ (b/d)τ_max I.

The ratio bound specializes positive-map contraction in Hilbert’s projective metric. The Lean argument proves the two endpoint inequalities directly.

**Theorem 1.2 (Bandwidth and bath dimension bounds).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermal_bandwidth_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermal_bandwidth_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. E. Allahverdyan, K. V. Hovhannisyan, D. Janzing and G. Mahler (2011). *Thermodynamic limits of dynamic cooling*. DOI: [10.1103/PhysRevE.84.041109](https://doi.org/10.1103/PhysRevE.84.041109). URL: <https://arxiv.org/abs/1107.1044v1>.

*Acknowledgement.* David Reeb, Michael J. Kastoryano and Michael M. Wolf (2011). *Hilbert’s projective metric in quantum information theory*. DOI: [10.1063/1.3615729](https://doi.org/10.1063/1.3615729). URL: <https://arxiv.org/abs/1102.5170v2>.

*Acknowledgement.* Fabien Clivaz, Ralph Silva, Géraldine Haack, Jonatan Bohr Brask, Nicolas Brunner and Marcus Huber (2019). *Unifying paradigms of quantum refrigeration: A universal and attainable bound on cooling*. DOI: [10.1103/PhysRevLett.123.170605](https://doi.org/10.1103/PhysRevLett.123.170605). URL: <https://arxiv.org/abs/1903.04970v2>.

*Commentary.*

At inverse temperature β > 0, an arbitrary finite Hermitian bath Hamiltonian of energy range W that prepares a positive definite target must satisfy βW ≥ log(μ_max/μ_min) and b ≥ dμ_max, where μ_min and μ_max are the target eigenvalue extremes.

The binary case follows from exact optimization over reservoir spectra for a maximally mixed target qubit. The bandwidth in this theorem is the range of the entire bath used in one joint unitary.

**Theorem 1.3 (The aligned Gibbs state).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.matching_bath`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.matching_bath` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

In the eigenbasis of a positive definite trace-one target, choose energies −β⁻¹ log μ_i. The normalized Gibbs state in that basis equals the target.

**Theorem 1.4 (The swap attains the spectral bandwidth).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.bandwidth_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.bandwidth_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Acknowledgement.* A. E. Allahverdyan, K. V. Hovhannisyan, D. Janzing and G. Mahler (2011). *Thermodynamic limits of dynamic cooling*. DOI: [10.1103/PhysRevE.84.041109](https://doi.org/10.1103/PhysRevE.84.041109). URL: <https://arxiv.org/abs/1107.1044v1>.

*Commentary.*

A bath indexed by the memory basis suffices. The tensor swap outputs the target on the memory and the maximally mixed state on the bath. The chosen energies have range β⁻¹ log(μ_max/μ_min).

**Theorem 1.5 (The normalized matrix exponential has Gibbs eigenweights).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermalState_eq_gibbsBath`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermalState_eq_gibbsBath` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

The repository thermal-state definition for a finite Hermitian Hamiltonian agrees with its diagonal Gibbs weights conjugated by the Hamiltonian eigenbasis.

**Theorem 1.6 (The Hermitian bath attains the lower bound).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermal_bandwidth_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermal_bandwidth_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

Conjugating the matching diagonal Hamiltonian into the eigenbasis of the target gives the minimizing physical matrix Hamiltonian. Its normalized matrix exponential supplies the input bath for the swap.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.bandwidth_attained`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.marginal_bounds`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.matching_bath`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermalState_eq_gibbsBath`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermal_bandwidth_attained`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidth.thermal_bandwidth_lower_bound`
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
