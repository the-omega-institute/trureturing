# Shifted energy on cyclic independent configurations

## Abstract

The compressed periodic hard-core Dirichlet form

**Theorem 1.1 (Flip and hop Laplacians).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedHamiltonian_eq_laplacians`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedHamiltonian_eq_laplacians` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Lesanovsky (2012). *Liquid ground state, gap and excited states of a strongly correlated spin chain*. DOI: [10.1103/PhysRevLett.108.105301](https://doi.org/10.1103/PhysRevLett.108.105301). URL: <https://arxiv.org/abs/1110.1815v1>.

*Commentary.*

For n ≥ 7, the diagonal n − |S| equals the weighted degree of the moves out of each independent configuration S. The shifted matrix is the flip-graph Laplacian plus one half of the hop-graph Laplacian.

Lesanovsky's constrained parent has the same equal-weight periodic ground state at z = 1. The operator here includes a half-weight nearest-neighbor hop, which supplies the row balance for the adjacent-marginal argument.

**Theorem 1.2 (Dirichlet form for complex amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedEnergy_eq_dirichlet`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedEnergy_eq_dirichlet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted energy is half the sum over ordered pairs of independent configurations of the transition weight times the squared modulus of their amplitude difference. The weights are one on flips and one half on hops. Splitting the amplitudes into real and imaginary parts gives the complex identity and shows nonnegativity.

**Theorem 1.3 (Zero energy forces equal amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedEnergy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedEnergy_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 7, the shifted energy is zero exactly when every amplitude equals the amplitude at the empty configuration. Each summand is nonnegative, so zero energy forces equality across each edge of positive weight. The deletion path from any independent configuration to the empty one uses only weight-one flips. Constant amplitudes make every squared difference zero.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedEnergy_eq_dirichlet`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedEnergy_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy.shiftedHamiltonian_eq_laplacians`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts](PeriodicMPSUniformHardCoreCounts.md)
