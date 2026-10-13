# Qubit Incompatibility Probability

## Abstract

The qubit incompatibility probability is strictly less than one quarter.

**Theorem 1.1 (One-quarter conjecture refuted).**

$$\neg \operatorname{OrderedRootCoordinates.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QubitIncompatibilityProbability.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-et-al-2019-qubit-incompatibility-probability` (refuted) by `D5/S3/Quantum/Measurement/QubitIncompatibilityProbability.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-et-al-2019-qubit-incompatibility-probability","declaration_gid":"D5/S3/Quantum/Measurement/QubitIncompatibilityProbability.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang; Hua Xiang; Xiao Li-Jost; Shao-Ming Fei (2019). *Incompatibility probability of random quantum measurements*. DOI: [10.1103/PhysRevE.100.062139](https://doi.org/10.1103/PhysRevE.100.062139). URL: <https://arxiv.org/abs/1912.12321>.

*Commentary.*

The exact probability is nine times a four-dimensional cube integral. The inequality sqrt(1-z) ≤ 1-z/2-z²/8 on [0,1], together with three explicit moments, gives the upper bound 5910272/23648625 < 1/4. Thus the probability in Section III.C of Zhang et al. differs from one quarter.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityProbability.result`
- Dependency: [D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction](QubitIncompatibilityRadialReduction.md)
