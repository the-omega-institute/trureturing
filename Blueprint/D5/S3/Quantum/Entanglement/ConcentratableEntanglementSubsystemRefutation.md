# Generalized concentratable entanglement is not monotone under enlarging the subsystem

## Abstract

Liu, Knörzer, Wang and Tura (arXiv:2406.18517, Phys. Rev. Research 7, L032022) define the generalized concentratable entanglement C^{(K)}_psi(s) = (1 - 2^{-|s|} sum_{alpha in P(s)} Tr(rho_alpha^K)) / (K - 1) of an n-qubit pure state, with Tr(rho_emptyset^K) = 1, and conjecture that C^{(K)}_psi(s') <= C^{(K)}_psi(s) whenever s' is a subset of s, for every real K > 1. It fails at K = 5/2 for a four-qubit state with integer amplitudes: removing one qubit from {0, 1, 2} raises the value.

**Definition 1.1 (The trace of a power of a reduced state).**

$$\forall N : \mathbb{N}, \forall K : \mathbb{R}, \forall psi : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, (\operatorname{powerTrace}\left(K, psi, \emptyset\right) = 1) \land (\forall alpha : \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right), (alpha \ne \emptyset) \Rightarrow (\operatorname{powerTrace}\left(K, psi, alpha\right) = \operatorname{ReTr}\left(\operatorname{reducedState}\left(alpha, psi\right)^{K}\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.powerTrace` (`✓ std3`).

*Citation.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Tr(rho_alpha^K) is the real part of the trace of the K-th power, in the continuous functional calculus, of the existing reducedState of psi on the qubits alpha; the empty set contributes 1, as the paper takes Tr(rho_emptyset^K) = 1.

**Definition 1.2 (Generalized concentratable entanglement).**

$$\forall N : \mathbb{N}, \forall K : \mathbb{R}, \forall psi : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, \forall s : \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right), \operatorname{gce}\left(K, psi, s\right) = \frac{1}{K - 1} \cdot (1 - \frac{1}{2^{|s|}} \cdot \sum_{alpha \subseteq s} \operatorname{powerTrace}\left(K, psi, alpha\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.gce` (`✓ std3`).

*Citation.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Eq. (defeq): C^{(K)}_psi(s) = (1 - 2^{-|s|} sum_{alpha in P(s)} Tr(rho_alpha^K)) / (K - 1), the sum running over all subsets alpha of s.

**Definition 1.3 (The conjectured monotonicity).**

$$(claim) \Leftrightarrow (\forall N : \mathbb{N}, \forall psi : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, (\sum_{w} \left\lVert psi\left(w\right) \right\rVert^{2} = 1) \Rightarrow (\forall t, s : \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right), (t \subseteq s) \Rightarrow (\forall K : \mathbb{R}, (1 < K) \Rightarrow (\operatorname{gce}\left(K, psi, t\right) \le \operatorname{gce}\left(K, psi, s\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.claim` (`✓ std3`).

*Citation.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Conjecture 1(1): for every number of qubits N, every normalized N-qubit vector psi, all subsets t of s of the qubits and every real K > 1, the value on t is at most the value on s.

**Definition 1.4 (The amplitudes).**

$$coeff = -1100 \cdot |0000\rangle - 100 \cdot |0101\rangle - 100 \cdot |1010\rangle + 75 \cdot |1100\rangle - 9 \cdot |1111\rangle$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

The unnormalized amplitudes are -1100, -100, -100, 75 and -9 on the basis states |0000>, |0101>, |1010>, |1100> and |1111>; their squares sum to 1235706.

**Definition 1.5 (The counterexample state).**

$$\forall w : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right)), psi\left(w\right) = \frac{coeff\left(w\right)}{\sqrt{1235706}}$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

The state is the amplitude vector divided by sqrt(1235706).

**Definition 1.6 (Coordinates of three qubits).**

$$\forall x : (\ \{0, 1, 2\ \} \to \operatorname{Fin}\left(2\right)), \operatorname{tripleEquiv}\left(x\right) = (x\left(0\right), x\left(1\right), x\left(2\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.tripleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

tripleEquiv reads a configuration x of the qubits {0, 1, 2} as (x(0), x(1), x(2)).

**Definition 1.7 (Coordinate outside three qubits).**

$$\forall z : (\operatorname{Outside}\left(\ \{0, 1, 2\ \}\right) \to \operatorname{Fin}\left(2\right)), \operatorname{out1Equiv}\left(z\right) = z\left(3\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.out1Equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

out1Equiv reads a configuration z of the qubit outside {0, 1, 2} as its value z(3).

**Theorem 1.8 (Enlarging the subsystem can lower the value).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-2025-gce-subsystem-monotonicity` (refuted) by `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-2025-gce-subsystem-monotonicity","declaration_gid":"D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Take N = 4, K = 5/2, t = {0, 1} and s = {0, 1, 2}. The reduced states of psi, scaled by 1235706, are: on one qubit diag(1220000, 15706) for the qubits 0 and 1 and diag(1225625, 10081) for the qubit 2; on {0, 1}, {0, 2} and {1, 2} a direct sum of diagonal entries and one 2 x 2 block, with block determinants 9900^2, 100^2 and 10000^2; on {0, 1, 2} the rank-two matrix u u^T + w w^T with u and w orthogonal of squared norms 1225625 and 10081. Each has an explicit positive semidefinite square root S: square roots of the diagonal entries, (M + sqrt(det M) I) / sqrt(tr M + 2 sqrt(det M)) on a 2 x 2 block M, and u u^T / |u| + w w^T / |w|. Hence rho^{5/2} = S^5 and Tr(rho^{5/2}) = Tr(Q^2 S) / 1235706^{5/2}. With T_alpha = Tr(rho_alpha^{5/2}), 8 (K - 1) (C(t) - C(s)) = T_2 + T_{02} + T_{12} + T_{012} - 1 - T_0 - T_1 - T_{01}; rational bounds for eight square roots show that it is about 5.77 * 10^{-7} > 0, so C^{(5/2)}({0, 1}) > C^{(5/2)}({0, 1, 2}).

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.coeff`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.gce`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.out1Equiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.powerTrace`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.psi`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.tripleEquiv`
- Dependency: [D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation](FourQubitResidualSumMonotoneRefutation.md)
