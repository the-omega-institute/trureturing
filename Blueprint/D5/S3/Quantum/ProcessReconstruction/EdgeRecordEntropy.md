# Entropy of the Paired Edge Record Law

## Abstract

The all-ones input block accounts for the entire entropy deficit of the paired law.

**Theorem 1.1 (Exact entropy of the paired weights).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy.pairedWeight_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy.pairedWeight_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Write d = 2ᴺ for a path of N sites. Divide the channel kernel by d to give the joint input-output weights under a uniform input. Every input row but the all-ones row has entries 1/d². The all-ones row has d/2 entries of weight 2/d² and d/2 zeros. The entropy is 2 log d − (log 2)/d in nats.

**Theorem 1.2 (The paired entropy profile gives an exact CMI).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy.pairedCMI_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy.pairedCMI_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

A proper mask of s sites has paired entropy 2s log 2. In the CMI combination for pairwise disjoint L, M, R, the size terms cancel. The full-mask deficit contributes only when the union is the whole path and both outer regions are nonempty. In that case the CMI is (log 2)/d.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy.pairedCMI_profile`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy.pairedWeight_entropy`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw](EdgeRecordLaw.md)
