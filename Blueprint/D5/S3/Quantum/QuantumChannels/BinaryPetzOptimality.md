# Binary Petz optimality for finite quantum records

## Abstract

Binary Petz optimality for finite quantum records

**Theorem 1.1 (Optimality from the visible blocks).**

Lean statement: `D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality.binary_petz_is_optimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality.binary_petz_is_optimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and E. Knill (2002). *Reversing quantum dynamics with near-optimal quantum and classical fidelity*. DOI: [10.1063/1.1459754](https://doi.org/10.1063/1.1459754).

*Commentary.*

Two rectangular amplitude matrices define the weighted hidden states. Their sum determines the inverse square root on its support. The first Petz effect and its full complement form an admissible binary measurement, including for a singular state sum.

The completed measurement attains the Helstrom contrast exactly when the two diagonal visible Gram blocks intertwine through the off-diagonal cross block.

**Theorem 1.2 (Exact periodic record criterion).**

Lean statement: `D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality.ring_physical_petz_is_optimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality.ring_physical_petz_is_optimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and E. Knill (2002). *Reversing quantum dynamics with near-optimal quantum and classical fidelity*. DOI: [10.1063/1.1459754](https://doi.org/10.1063/1.1459754).

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For the two fair-prior complementary states of the primitive periodic collision, the transposed support Petz effect minimizes the physical discrimination error precisely when the total ring length is divisible by four. The statement applies in the common-marginal range from seven sites onward.

The finite ring enters through its actual partial trace and exact cross reduction. The error criterion concerns a static binary measurement.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality.binary_petz_is_optimal_iff`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/BinaryPetzOptimality.ring_physical_petz_is_optimal_iff`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Lieb/SupportPerspectiveTransport](../Lieb/SupportPerspectiveTransport.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](PositiveFilterTransposeRefutation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator](../TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator.md)
