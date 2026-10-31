# Achievable (k-fidelity, process fidelity) regions and single-fidelity non-identifiability

## Abstract

Exact planar regions of pairs (F_k(Lambda), F(Lambda)) realized by n-qubit completely positive trace-preserving maps across k = 0, 1 <= k <= n - 1, and k >= n, closed-form upper and lower process-fidelity envelopes at prescribed 0-fidelity, unimodal maximizer analysis of the binomial weight kernel, and non-identifiability of F(Lambda) from any single F_k(Lambda) for n >= 2 and k <= n - 1.

**Definition 1.1 (Achievable (k-fidelity, process fidelity) region).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits and truncation order k, achievableRegion(n, k, rho) is the subset of R^2 consisting of all pairs (realKFidelity(rho, k, Lambda), realProcessFidelity(Lambda)) as Lambda ranges over completely positive trace-preserving n-qubit maps.

**Definition 1.2 (Unsigned Pauli-weight binomial kernel).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.tailCoeff`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.tailCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines g_k(w) = 3^{-w} C(w - 1, k) for natural numbers k and w.

**Definition 1.3 (Maximizing Hamming weight w*).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.optWeight`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.optWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines w*(n, k) = min(n, floor(3 k / 2) + 1).

**Definition 1.4 (Signed extremal horizontal vertex abscissa).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.extremalAbscissa`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.extremalAbscissa` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines x_k(n) = (-1)^k g_k(w*(n, k)), the nonzero horizontal coordinate among vertices on the axis F = 0 for 1 <= k <= n - 1.

**Theorem 1.5 (Exact 0-fidelity achievable triangle, single-qubit segment, and extremal envelopes).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_zero_characterization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_zero_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n >= 1, R_0 equals the closed convex hull of (1, 1), (3^{-n}, 0), and (1 / 3, 0). When n >= 2, (F_0, F) belongs to R_0 if and only if F >= 0 and 1 - (3 / 2)(1 - F_0) <= F <= (F_0 - 3^{-n}) / (1 - 3^{-n}), with the upper edge attained by mixtures t id + (1 - t) Z^{tensor n} (.) Z^{tensor n} and the lower edge attained by weight-1 Pauli mixtures; at every prescribed F_0 in [3^{-n}, 1], the maximum of F is (F_0 - 3^{-n}) / (1 - 3^{-n}) (strictly below F_0 for F_0 < 1 with gap (1 - F_0) 3^{-n} / (1 - 3^{-n})) and the minimum of F is max(0, 1 - (3 / 2)(1 - F_0)). When n = 1, R_0 collapses to the line segment F = 1 - (3 / 2)(1 - F_0) over 1 / 3 <= F_0 <= 1.

**Theorem 1.6 (Intermediate achievable triangles, unimodal maximizers, and high-order diagonal segment).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_intermediate_and_high_characterization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_intermediate_and_high_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For 1 <= k <= n - 1, the kernel g_k(w) = 3^{-w} C(w - 1, k) satisfies 0 < g_k(w*) < 1 and attains its maximum over 1 <= w <= n uniquely at w* = min(n, floor(3 k / 2) + 1), except when k is even and 3 k / 2 + 1 <= n where the maximum is attained at {3 k / 2, 3 k / 2 + 1}; the achievable region R_k is the closed triangle conv{(1, 1), (0, 0), (x_k, 0)}, cut out by F >= 0 and F_k <= F <= (F_k - x_k) / (1 - x_k) for odd k and by F >= 0 and (F_k - x_k) / (1 - x_k) <= F <= F_k for even k (implying 0 <= F <= 1), with vertices attained by the identity map, weight-1 Pauli conjugation, and weight-w* Pauli conjugation. For k >= n >= 1, R_k is the diagonal segment {(F_k, F) | F_k = F and 0 <= F <= 1}.

**Theorem 1.7 (Non-identifiability of process fidelity from a single lower-order k-fidelity).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.kFidelity_non_identifiability_of_processFidelity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.kFidelity_non_identifiability_of_processFidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n >= 2 and every 0 <= k <= n - 1, there exist two n-qubit completely positive trace-preserving maps with the same k-fidelity F_k, one having zero entanglement process fidelity and one having strictly positive entanglement process fidelity (and hence distinct process fidelities).

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_intermediate_and_high_characterization`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_zero_characterization`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.extremalAbscissa`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.kFidelity_non_identifiability_of_processFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.optWeight`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.tailCoeff`
- Dependency: [D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight](SicKFidelityPauliWeight.md)
