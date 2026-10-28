# CanonicalFlagCompression

## Abstract

Canonical CPTP maps with classical flag outputs have the same component-dimension bound as normalized finite Kraus ports.

The encoder and decoder use the existing canonical all-amplification completely positive trace-preserving channel interface. Classical output means that distinct flag sectors have zero matrix entries for every matrix input; it imposes no input independence on flag probabilities. Their canonical finite Kraus representations restrict to encoder rows and decoder columns in each flag sector. Trace preservation normalizes the encoder jointly and the decoder separately on each entire coherent block. The encoded matrices are block diagonal, so their actual decoder action is exactly the same-flag rectangular Kraus composite. The probability-preserving component lower bound therefore applies directly to arbitrary canonical channels in the classical-quantum compression model of Bluhm, Rauber, and Wolf.

**Theorem 1.1 (canonical flag port factorization).**

Lean statement: `D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Commentary.*

Any canonical CPTP encoder with classical flag output and canonical CPTP decoder admit a normalized finite Kraus port with identical all-matrix composite action.

**Theorem 1.2 (canonical flag port lower bound).**

Lean statement: `D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

For arbitrary unit probe families and arbitrary finite classical flags, canonical CPTP encoding and decoding that preserve every probe probability for every density input have coherent block dimension at least every actual component dimension.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_factorization`
- Truth anchor: `D5/S3/Quantum/Reduction/CanonicalFlagCompression.canonical_flag_port_lower_bound`
- Dependency: [D5/S3/Quantum/Reduction/CoherentFlagPort](CoherentFlagPort.md)
