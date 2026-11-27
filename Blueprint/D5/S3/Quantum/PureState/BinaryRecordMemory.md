# Finite memory for binary pure records

## Abstract

Walsh weights give an explicit compression penalty, and overlap-one pairs reduce the occupied span.

**Theorem 1.1 (The phase penalty on the original heterogeneous product carrier).**

Lean statement: `D5/S3/Quantum/PureState/BinaryRecordMemory.coordinateProductRecord_success_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BinaryRecordMemory.coordinateProductRecord_success_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yonina C. Eldar, G. David Forney Jr. (2001). *On quantum detection and the square-root measurement*. DOI: [10.1109/18.915636](https://doi.org/10.1109/18.915636). URL: <https://arxiv.org/abs/quant-ph/0005132>.

*Commentary.*

For k independent fair bits, let sᵢ be each normalized pair's overlap modulus and assume every sᵢ is below one. Write N = 2ᵏ and g for the uncompressed joint optimum, the product of (1 + sqrt(1 − sᵢ²)) / 2. An arbitrary CPTP encoder from the original product carrier to dimension M, followed by an output POVM, has success at most min(M / N, g − (1 − M / N) c). Here c is the product of (1 − sᵢ + sqrt(1 − sᵢ²)) / 2.

The product optimum uses the Walsh measurement, a case of the square-root measurement in Theorem 4 of Eldar and Forney. Isometric transport and the phase dual gap supply the CPTP memory bound.

**Theorem 1.2 (Strict overlaps give an exact threshold of 2ᵏ).**

Lean statement: `D5/S3/Quantum/PureState/BinaryRecordMemory.coordinateProductRecord_optimum_attainable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BinaryRecordMemory.coordinateProductRecord_optimum_attainable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When all local overlap moduli are below one, the full joint optimum on the original product carrier is attainable through a CPTP memory exactly when its dimension is at least 2ᵏ. The local carriers may have different dimensions. The threshold specializes the known pure-state uniqueness and dimension argument to the occupied Walsh span.

**Theorem 1.3 (A uniform duplicate label scales the whole attainable success set).**

Lean statement: `D5/S3/Quantum/PureState/BinaryRecordMemory.repeatedLabel_success_set`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BinaryRecordMemory.repeatedLabel_success_set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For uniform labels (x, y) whose conditional states depend only on x, sum the labelled effects over y to obtain a POVM for x. The success values for guessing the pair are exactly the success values for guessing x divided by the size of the nonempty y-type. A fixed y-guess lifts any POVM for x.

**Theorem 1.4 (Overlap-one coordinates affect the guessing value and reduce the required memory).**

Lean statement: `D5/S3/Quantum/PureState/BinaryRecordMemory.activeProductRecord_optimum_and_memory`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BinaryRecordMemory.activeProductRecord_optimum_and_memory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary normalized binary pairs, let r count the overlap-one coordinates. The attained whole-word optimum is 2⁻ʳ times the product of the single-coordinate optima over the k − r active coordinates. A CPTP memory attains that value exactly when its dimension is at least 2 raised to k − r. After rephasing, each repeated pair gives the same conditional density for either bit. The active Walsh carrier transports isometrically and the repeated labels aggregate.

## References

- Truth anchor: `D5/S3/Quantum/PureState/BinaryRecordMemory.activeProductRecord_optimum_and_memory`
- Truth anchor: `D5/S3/Quantum/PureState/BinaryRecordMemory.coordinateProductRecord_optimum_attainable_iff`
- Truth anchor: `D5/S3/Quantum/PureState/BinaryRecordMemory.coordinateProductRecord_success_le`
- Truth anchor: `D5/S3/Quantum/PureState/BinaryRecordMemory.repeatedLabel_success_set`
- Dependency: [D5/S3/Quantum/PureState/BinaryPureRecordDecoding](BinaryPureRecordDecoding.md)
- Dependency: [D5/S3/Quantum/PureState/PhaseRecordMemory](PhaseRecordMemory.md)
