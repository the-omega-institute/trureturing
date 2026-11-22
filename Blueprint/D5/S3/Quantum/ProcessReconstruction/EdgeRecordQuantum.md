# Normalized Choi States of the Edge Record Channels

## Abstract

The edge record channels have maximally mixed proper paired windows and an exact Choi CMI profile.

**Theorem 1.1 (The reference-first normalized Choi state is diagonal).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.choi_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.choi_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Apply the channel to the input half of the normalized Bell state. The matrix unit entry formula gives the diagonal Choi weights Kᵦ(y|x)/d in reference-output order, where d = 2ᴺ and N is the number of sites.

**Theorem 1.2 (Every proper output reduction is a mixed replacer).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.proper_output_replacer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.proper_output_replacer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Retaining any proper set of output sites yields the maximally mixed state times the trace of the full input matrix. This equality holds on the full matrix algebra.

**Theorem 1.3 (All proper paired Choi windows are maximally mixed).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.proper_paired_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.proper_paired_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Keep each selected input reference with its corresponding output. Each proper set of s paired sites gives the identity divided by 4ˢ, for either channel. This holds for every proper subset and hence for every contiguous window of width less than N, uniformly in the window and path size.

**Theorem 1.4 (Exact conditional mutual information of paired sites).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.choi_pairedCMI`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.choi_pairedCMI` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The full normalized Choi entropy is 2 log d − (log 2)/d. For pairwise disjoint L, M, R, the paired CMI is (log 2)/d if their union is full and both L and R are nonempty. It is zero in every other case.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.choi_diagonal`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.choi_pairedCMI`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.proper_output_replacer`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum.proper_paired_mixed`
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation](../Information/ChenKatoBrandaoCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](../Information/InputInformationBalance.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy](EdgeRecordEntropy.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction](LiuWildChoiObstruction.md)
