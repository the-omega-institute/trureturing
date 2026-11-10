# An explicit source amplitude

## Abstract

The six-dimensional reverse instance with the literal twelve-dimensional source environment.

The input is a qubit, the output is a qubit times a three-level system, and the source environment is the input times a copy of that output. The active amplitude is Y = 3I + sigma-x tensor diag(1,-1,0) + sigma-z tensor (E02+E20). The source permutation exchanges the reference qubit and the binary output coordinate. The unused environment coordinates are retained.

**Theorem 1.1 (The physical channel).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseDecoder.physical_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseDecoder.physical_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicitly specified twelve-label Kraus family is normalized and defines a completely positive, trace-preserving map in the canonical quantum-channel interface. Its output on the maximally mixed qubit is Y squared divided by 62.

**Theorem 1.2 (The active rotation).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseDecoder.rotation_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseDecoder.rotation_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four real rotation parameters satisfy two unit-circle equations. These equations imply both unitary identities for the active six-dimensional matrix.

**Theorem 1.3 (Literal source rows).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseDecoder.supported_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseDecoder.supported_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After adjoining the fixed zero ancilla, the actual source permutation maps every physical output into the active six-dimensional source support. The composite source Kraus operators are the active rotation rows; all other environment labels give zero.

**Theorem 1.4 (A positive polynomial gap).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseDecoder.gap_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseDecoder.gap_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the two circle equations and a strictly positive sum of sine parameters, the displayed sum-of-squares certificate gives a strictly positive polynomial gap. This statement alone does not identify either decoder fidelity. The positive polar product, the ordinary Petz identity, and the canonical-purification comparison are additional mathematical obligations.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseDecoder.gap_positive`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseDecoder.physical_channel`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseDecoder.rotation_unitary`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseDecoder.supported_rows`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/ReferencePetzChannel](ReferencePetzChannel.md)
