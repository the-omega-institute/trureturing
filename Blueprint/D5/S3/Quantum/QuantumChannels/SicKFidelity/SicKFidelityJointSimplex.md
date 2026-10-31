# Trace-preserving linear reconstruction and CPTP joint k-fidelity simplex geometry

## Abstract

Universal alternating linear relation among F_0, ..., F_{n-1} and the entanglement process fidelity F for arbitrary trace-preserving linear qubit maps, affine independence of the n + 1 Pauli-weight vertices in R^n, and exact n-simplex characterization of the joint CPTP k-fidelity range with unique barycentric recovery of (Q_0, ..., Q_n) and F.

**Definition 1.1 (Joint k-fidelity simplex vertices).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.simplexVertex`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.simplexVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines the n + 1 vectors V_0, ..., V_n in R^n by V_0 = (1, ..., 1) and (V_w)_k = (-1)^k 3^{-w} C(w - 1, k) for 1 <= w <= n and 0 <= k <= n - 1.

**Definition 1.2 (Joint lower-order k-fidelity vector).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.jointKFidelityVec`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.jointKFidelityVec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Collects the first n real SIC k-fidelities (F_0(Lambda), ..., F_{n-1}(Lambda)) in R^n for an n-qubit map Lambda.

**Definition 1.3 (CPTP joint k-fidelity range).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.jointKFidelityRange`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.jointKFidelityRange` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines the subset of R^n consisting of all joint vectors (F_0(Lambda), ..., F_{n-1}(Lambda)) realized by completely positive trace-preserving n-qubit maps Lambda.

**Theorem 1.4 (Universal linear relation and exact fidelity reconstruction for trace-preserving maps).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.tp_exact_fidelity_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.tp_exact_fidelity_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n, every choice of single-qubit SICs, and every trace-preserving complex-linear map Lambda on M_{2^n}(C) (without requiring complete positivity), 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda) + (-2)^n F(Lambda) = 1, equivalently F(Lambda) = (-2)^{-n} (1 - 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda)), together with the corresponding real identity when Lambda is completely positive.

**Theorem 1.5 (Affine independence, n-simplex joint range, and unique barycentric Pauli-weight recovery).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.cptp_joint_kFidelity_simplex_range`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.cptp_joint_kFidelity_simplex_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n >= 1, the n + 1 vertices V_0, ..., V_n in R^n are affinely independent, the set of joint k-fidelity vectors (F_0(Lambda), ..., F_{n-1}(Lambda)) over completely positive trace-preserving n-qubit maps equals the n-simplex conv{V_0, ..., V_n}, the Pauli-weight sums (Q_0(Lambda), ..., Q_n(Lambda)) are the unique barycentric coordinates of (F_0(Lambda), ..., F_{n-1}(Lambda)) in this simplex, and F(Lambda) = Q_0(Lambda) = (-2)^{-n} (1 - 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda)).

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.cptp_joint_kFidelity_simplex_range`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.jointKFidelityRange`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.jointKFidelityVec`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.simplexVertex`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.tp_exact_fidelity_reconstruction`
- Dependency: [D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight](SicKFidelityPauliWeight.md)
