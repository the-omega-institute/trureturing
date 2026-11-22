# Diamond Reconstruction Limits for Edge Record Channels

## Abstract

Uniform paired Choi CMI decay coexists with maximal diamond separation and an exact-data minimax lower bound.

**Theorem 1.1 (A uniform bound in the middle region size).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.choi_pairedCMI_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.choi_pairedCMI_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

For either channel and any pairwise disjoint regions L, M, R, the paired Choi CMI in nats is at most (log 2) exp(−(log 2)|M|). The prefactor and decay length in Liu–Wild Definition 1 are log 2 and 1/log 2, independent of the path length.

**Theorem 1.2 (The normalized Choi trace norm difference is 2/d).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.choi_traceNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.choi_traceNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The Choi states differ only at the all-ones reference word. The two opposite parity blocks there have disjoint supports and each has mass 1/d, where d = 2ᴺ. Their unhalved trace norm difference is 2/d.

**Theorem 1.3 (The all-ones product probe distinguishes the pair).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.product_probe_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.product_probe_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

One call on the all-ones computational product input followed by a global output parity measurement returns the channel bit with probability one.

**Theorem 1.4 (The unhalved diamond distance is 2).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.maximal_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.maximal_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The all-ones product input gives output trace norm difference 2, attaining the universal upper bound on the unhalved diamond distance between channels.

**Theorem 1.5 (Any exact proper paired data estimator incurs diamond error at least 1).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.pairedData_minimax`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.pairedData_minimax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

On each finite path the two channels give the same family of exact proper paired marginals, so every channel-valued function of the entire family returns one common estimate. The maximum of its two unhalved diamond errors is at least 1. This bound also applies to data restricted to proper windows of any fixed width smaller than the path.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.choi_pairedCMI_decay`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.choi_traceNorm`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.maximal_diamond`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.pairedData_minimax`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance.product_probe_parity`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum](EdgeRecordQuantum.md)
