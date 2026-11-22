# Coherent Query Lower Bounds for Hidden Inputs

## Abstract

The uniform-oracle hybrid yields a lower bound for adaptive protocols with arbitrary finite quantum memory.

**Theorem 1.1 (Worst-case parity discrimination requires at least 2ᴺ/3 calls).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound.query_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound.query_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Use an arbitrary joint initial state, sequential channel calls and arbitrary CPTP interleavings on the query register and finite memory. The terminal binary measurement may depend on the mark revealed after the last call. Success of at least two thirds at every mark and parity forces T ≥ 2ᴺ/3. Rosenthal et al., Theorem 1.2 and Section 3, use rare input weights for replacement-channel certification.

**Theorem 1.2 (Finite-outcome diamond reconstruction requires at least 2ᴺ/3 calls).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound.reconstruction_query_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound.reconstruction_query_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

A finite terminal POVM yields a channel estimate at each outcome. At each member of the family the event of unhalved diamond error strictly below one must have probability at least two thirds.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound.query_lower_bound`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound.reconstruction_query_lower_bound`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels](EdgeRecordQueryChannels.md)
