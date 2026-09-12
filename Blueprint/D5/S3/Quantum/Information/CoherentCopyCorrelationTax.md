# Coherent Premeasurement and Correlation Tax

## Abstract

A coherent premeasurement retains the input entropy and divides system-record mutual information into diagonal entropy and relative entropy of coherence.

The copying isometry sends basis vector i to the joint basis vector (i,i). The joint state is V rho V*, including the input's off-diagonal entries. Both marginals are obtained by partial trace.

**Theorem 1.1 (Coherence survives on the correlated subspace).**

$$\forall \rho, i, j, \operatorname{jointEntry}\left(\rho, i, j\right) = \operatorname{inputEntry}\left(\rho, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherentCopyState_correlated_entry` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For every input density state and every pair of indices, the joint matrix entry at (i,i),(j,j) equals the input entry at i,j.

**Theorem 1.2 (The system marginal is the pinched input).**

$$\forall \rho, \operatorname{marginalRight}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{basisPinchingState}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalRight_coherentCopyState` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Tracing out the record leaves precisely the diagonal of the input.

**Theorem 1.3 (The record marginal has the Born weights).**

$$\forall \rho, \operatorname{marginalLeft}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{basisPinchingState}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalLeft_coherentCopyState` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Tracing out the system produces the same diagonal state: its ith diagonal entry is rho(i,i), and its off-diagonal entries vanish.

**Theorem 1.4 (Coherent copying preserves entropy).**

$$\forall \rho, \operatorname{vonNeumannEntropy}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{vonNeumannEntropy}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.vonNeumannEntropy_coherentCopyState` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The copying map preserves multiplication, adjoints and trace. Functional calculus transports the logarithm through this map, including zero eigenvalues, so the entropy trace is unchanged.

**Theorem 1.5 (Correlation equals record entropy plus coherence tax).**

$$\forall \rho, \operatorname{quantumMutualInformation}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{vonNeumannEntropy}\left(\operatorname{basisPinchingState}\left(\rho\right)\right) + \operatorname{quantumRelativeEntropy}\left(\rho, \operatorname{basisPinchingState}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherent_copy_correlation_tax` (`✓ std3`). ∎

*Citation.* T. Baumgratz, M. Cramer, M. B. Plenio (2014). *Quantifying Coherence*. URL: <https://arxiv.org/abs/1311.0275v3>.

*Commentary.*

The two marginal entropies are the diagonal entropy, and the joint entropy is the original entropy. The pinching entropy identity supplies the remaining relative entropy term.

## References

- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherentCopyState_correlated_entry`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherent_copy_correlation_tax`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalLeft_coherentCopyState`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalRight_coherentCopyState`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.vonNeumannEntropy_coherentCopyState`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
