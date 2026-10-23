# CoherentFlagPort

## Abstract

Finite classical flags do not lower the necessary coherent dimension below a preserved probe component; explicit complement-filled decoders are trace preserving on entire port blocks.

A finite port consists of actual rectangular encoder and decoder Kraus families. The encoder is normalized jointly over flags; the decoder is normalized separately for every flag on the entire coherent block. Flag probabilities may depend on the input. The actual encoder and decoder also have canonical completely positive trace-preserving realizations on the ambient flagged matrix algebra; their Kraus matrices encode only classical diagonal sectors and discard cross-sector coherences during decoding. Every composite Kraus matrix factors through the same port index space, so its rank is at most that coherent dimension. Probability preservation gives scalar action on each component. Normalization guarantees a nonzero scalar on each component, forcing its dimension below the port dimension. For a partial isometry J with adjoint Gram projection P, the decoder maps Y to J adjoint times Y times J plus the trace of the unused port complement times a fixed density. This acts on all matrices in the port block. The fixed density is a sum of rank-one factors of total squared norm one; choosing these factors inside the component makes it supported there. Bluhm, Rauber, and Wolf Sections 4 and 7.1 supply the classical-quantum compression model and the maximal-block construction.

**Theorem 1.1 (flagged cptp roundtrip).**

Lean statement: `D5/S3/Quantum/Reduction/CoherentFlagPort.flagged_cptp_roundtrip`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/CoherentFlagPort.flagged_cptp_roundtrip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Every normalized rectangular finite flagged port admits canonical completely positive trace-preserving encoder and decoder maps. The encoder image is proved to have zero entries between distinct classical flag sectors for every matrix input. Their all-matrix composition is exactly the same-flag Kraus composite used by the coherent dimension lower bound.

**Theorem 1.2 (port component lower bound).**

Lean statement: `D5/S3/Quantum/Reduction/CoherentFlagPort.port_component_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/CoherentFlagPort.port_component_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Any normalized finite flagged port preserving all probe probabilities on every density input has coherent dimension at least the complex dimension of each probe component span.

**Theorem 1.3 (padded decoder cptp).**

Lean statement: `D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_cptp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_cptp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

For a partial-isometry Gram projection and a normalized finite fixed-state factorization, the explicit decoder Kraus family is normalized and supplies a canonical completely positive trace-preserving channel. Its all-matrix action includes the fixed-state complement filler.

**Theorem 1.4 (padded decoder corner).**

Lean statement: `D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_corner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The same whole-block decoder maps every encoded component corner to P times the original matrix times P, with vanishing filler contribution.

**Theorem 1.5 (component pinching port).**

Lean statement: `D5/S3/Quantum/Reduction/CoherentFlagPort.component_pinching_port`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/CoherentFlagPort.component_pinching_port` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

A complete finite family of component projections, partial-isometry embeddings into one coherent block, and normalized fixed-state factors determines an actual finite flagged port whose composite equals the component pinching map on every matrix.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/CoherentFlagPort.component_pinching_port`
- Truth anchor: `D5/S3/Quantum/Reduction/CoherentFlagPort.flagged_cptp_roundtrip`
- Truth anchor: `D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_corner`
- Truth anchor: `D5/S3/Quantum/Reduction/CoherentFlagPort.padded_decoder_cptp`
- Truth anchor: `D5/S3/Quantum/Reduction/CoherentFlagPort.port_component_lower_bound`
- Dependency: [D5/S3/Quantum/Reduction/ProbeComponentRigidity](ProbeComponentRigidity.md)
