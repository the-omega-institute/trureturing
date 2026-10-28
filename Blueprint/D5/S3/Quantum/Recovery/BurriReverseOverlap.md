# Actual Kraus overlaps

## Abstract

Canonical purified overlaps for the two explicit recovery channels.

The recovered density matrix applies the amplified composite Kraus operators to the canonical maximally entangled purification of the maximally mixed qubit. Both original twelve-dimensional environment label sets occur in the composite, with a bijective finite reindexing.

**Theorem 1.1 (Purification and Kraus sums).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseOverlap.purification_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseOverlap.purification_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical purification overlap equals the sum of squared moduli of one-half the traces of the actual composite Kraus matrices. This is derived from the amplified map; the trace formula is not an assumption.

**Theorem 1.2 (Normalized recovery channels).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseOverlap.recovery_channels`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseOverlap.recovery_channels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal source-row construction and the environment-slice construction both define completely positive, trace-preserving channels on the six-dimensional physical output.

**Theorem 1.3 (A strict canonical overlap gap).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseOverlap.canonical_overlap_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseOverlap.canonical_overlap_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the fixed radical rotation, the source-row recovery has strictly smaller canonical purified overlap than the slice recovery, whose overlap is 27/31. The proof uses the exact polynomial certificate. Identifying the slice recovery with ordinary Petz and identifying all padded source SVD completions remain additional obligations; this comparison alone does not assert a resolution of Burri's question.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseOverlap.canonical_overlap_gap`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseOverlap.purification_overlap`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseOverlap.recovery_channels`
- Dependency: [D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness](../QuantumChannels/MayerZeroFidelityTightness.md)
- Dependency: [D5/S3/Quantum/Recovery/BurriReversePolar](BurriReversePolar.md)
