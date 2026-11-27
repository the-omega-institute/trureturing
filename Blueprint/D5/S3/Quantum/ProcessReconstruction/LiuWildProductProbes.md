# Optimal Adaptive Product Probes for an Explicit Channel Pair

## Abstract

Fresh product inputs yield exponentially small per-call separation of two explicit channels.

The testing curve holds for n ≥ 1 qubits. Each channel has Kraus rank two for n ≥ 2. The two channels induce identical reduced maps on every proper output subset, even with a retained reference. A full-output measurement on a GHZ input distinguishes them in one call.

**Theorem 1.1 (One-call total variation with any global output measurement).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.product_probe_totalVariation_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.product_probe_totalVariation_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

A fresh mixed product input creates at most 2/2ⁿ variation between the outcome laws for the two channels, for any finite measurement on the full output. The matrix entry joining the two antipodal words factors over the sites.

**Theorem 1.2 (Sharp worst-case success after a fixed number of calls).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.liu_wild_product_input_worst_case_success_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.liu_wild_product_input_worst_case_success_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

For each of M calls, the policy chooses a fresh tensor product of single-qubit density states and a finite POVM on that call’s full output. The choices use only the classical history and a finite seed with the same law under both hypotheses. The worst-case success is at most 1 − (1 − 2/2ⁿ)^M/2. Success of at least two thirds requires at least 2ⁿ/6 calls.

**Theorem 1.3 (Repeated all-plus probes attain the bound).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.liu_wild_product_input_success_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.liu_wild_product_input_success_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

The three-outcome measurement projects onto the two antipodal GHZ directions and their orthogonal complement. The correct conclusive outcome has probability 2/2ⁿ. If every call is inconclusive, a shared fair random bit guesses the channel. This protocol attains the bound on each channel.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.liu_wild_product_input_success_attained`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.liu_wild_product_input_worst_case_success_le`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes.product_probe_totalVariation_le`
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](../../Estimation/DecisionRisk/DescentDefectBounds.md)
- Dependency: [D5/S3/Estimation/LeCam](../../Estimation/LeCam.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess](RankTwoHiddenProcess.md)
