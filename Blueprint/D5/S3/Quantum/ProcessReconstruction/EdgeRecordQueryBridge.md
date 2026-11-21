# Query Hardness of Product-Environment Path Channels

## Abstract

The hidden-input oracles are the edge-record channels after site-local input bit flips.

**Theorem 1.1 (The original uniform edge and site records give the marked row law).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.markedMass_eq_push`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.markedMass_eq_push` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Translate the input word x to x + (allOn − a). Only the marked word a becomes all ones. The original local record map produces the uniform law on the parity-b fiber at a and the full uniform law elsewhere.

**Theorem 1.2 (The hidden-input oracle equals the translated path channel).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.markedChannel_eq_activatedChannel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.markedChannel_eq_activatedChannel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The equal row laws identify the prepared density states, giving equality of the two CPTP maps.

**Theorem 1.3 (The translated record isometry realizes the channel on every input matrix).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.trace_activatedDilation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.trace_activatedDilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Permute the input columns of the original isometry by the site-local translation. Its environment partial trace gives the translated channel. In the paper circuit, the translation is one parallel layer of input bit flips before the original ten-layer schedule, with the same pure product environment initialization.

**Theorem 1.4 (Every proper paired marginal agrees across all marks and parities).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_properPairedData_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_properPairedData_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

In the normalized Choi state the translation relabels the input reference indices. The permutation splits across kept and discarded sites, so the original maximally mixed proper marginals are unchanged.

**Theorem 1.5 (The same uniform Choi CMI decay holds throughout the family).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_pairedCMI_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_pairedCMI_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The relabeling preserves every paired entropy, including that of the full Choi state. For disjoint L, M, R the CMI therefore obeys (log 2) exp(−(log 2)|M|) throughout the family, in nats.

**Theorem 1.6 (The translated path family requires at least 2ᴺ/3 calls for discrimination).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_query_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_query_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

One protocol must succeed with probability at least two thirds on each mark and parity. Its probes and CPTP interleavings may use arbitrary finite quantum memory, and the decision may receive the mark after the calls. A known mark can be queried directly in the computational basis.

**Theorem 1.7 (The translated path family requires at least 2ᴺ/3 calls for diamond reconstruction).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_reconstruction_query_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_reconstruction_query_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The same bound applies when a finite POVM outcome selects a channel estimate and the unhalved diamond error is strictly below one with probability at least two thirds on every member. The accompanying paper algorithm uses O(2ᴺ) channel calls under the family promise.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_pairedCMI_decay`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_properPairedData_eq`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_query_lower_bound`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.activated_reconstruction_query_lower_bound`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.markedChannel_eq_activatedChannel`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.markedMass_eq_push`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge.trace_activatedDilation`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/EdgeRecordDilation](EdgeRecordDilation.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance](EdgeRecordDistance.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound](EdgeRecordQueryBound.md)
