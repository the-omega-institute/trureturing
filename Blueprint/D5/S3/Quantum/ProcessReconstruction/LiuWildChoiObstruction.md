# Diamond Reconstruction Limits under Choi Conditional Mutual Information Decay

## Abstract

Uniform exponential Choi conditional mutual information decay permits maximal diamond distance under identical proper-window data.

**Theorem 1.1 (Identical proper Choi windows and maximal diamond distance).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction.uniform_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction.uniform_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Pair each input reference with its corresponding output site. On any register of at least two qubits, the two unital rank-two channels have identical normalized Choi marginals on every proper paired window. The trace norm of their normalized Choi difference is 4/2ⁿ and their unhalved diamond distance is 2.

Each paired marginal has rank at most three and large overlap with a product of Bell states. These properties give a uniform exponential conditional mutual information bound in nats in the size of the middle region.

**Theorem 1.2 (Worst-case diamond reconstruction error from proper windows).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction.paired_data_minimax`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction.paired_data_minimax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

Any reconstruction function of the exact proper paired marginals must return the same estimate for the two channels. Its unhalved diamond error is at least 1 on one of them. The uniform conditional mutual information bound puts both channels in the class used in Liu and Wild's local tomography guarantee.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction.paired_data_minimax`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction.uniform_obstruction`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity](../Information/StrongSubadditivity.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess](RankTwoHiddenProcess.md)
