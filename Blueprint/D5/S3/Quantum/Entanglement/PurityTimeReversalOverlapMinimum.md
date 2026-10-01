# The minimum of purity plus time-reversal overlap

## Abstract

For every bipartition of N qubits into a part A of k qubits and its non-empty complement, the minimum over pure states of the purity of the reduced state plus its overlap with the time-reversed reduced state is 2^(k-N) when 2k > N and 2^(1-k) when 2k <= N. This proves Conjecture 2 of E. Serrano-Ensastiga, O. Giraud and J. Martin (arXiv:2507.12680), who proved the case k = 1 and found the other values numerically for up to ten qubits.

**Definition 1.1 (The reduced state).**

$$\operatorname{reducedState}\left(A, psi, x, y\right) = \sum_{z} psi\left(x, z\right) \cdot \operatorname{conj}\left(psi\left(y, z\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.reducedState` (`✓ std3`).

*Citation.* Eduardo Serrano-Ensástiga; Olivier Giraud; John Martin (2026). *Multiqubit monogamy relations beyond shadow inequalities*. DOI: [10.1103/9fkf-hm8l](https://doi.org/10.1103/9fkf-hm8l). URL: <https://arxiv.org/abs/2507.12680v2>.

*Commentary.*

For a set A of qubits among N and a vector psi of amplitudes on the configurations of the N qubits, the reduced state rho_A is the partial trace over the qubits outside A of the outer product of psi with itself, written on pairs (x, z) of configurations of A and of the other qubits: its entry at x, y is the sum over z of psi(x, z) times the complex conjugate of psi(y, z).

**Definition 1.2 (The time-reversed state).**

$$\operatorname{timeReversed}\left(A, rho\right) = Y \cdot \operatorname{conj}\left(rho\right) \cdot Y$$

*Formalization.* `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.timeReversed` (`✓ std3`).

*Citation.* Eduardo Serrano-Ensástiga; Olivier Giraud; John Martin (2026). *Multiqubit monogamy relations beyond shadow inequalities*. DOI: [10.1103/9fkf-hm8l](https://doi.org/10.1103/9fkf-hm8l). URL: <https://arxiv.org/abs/2507.12680v2>.

*Commentary.*

With sigma_y = i X Z for the qubit Pauli matrices X and Z, and Y the k-fold tensor power of sigma_y on the qubits of A, whose entry at configurations x, y of A is the product over the qubits i of A of sigma_y(x_i, y_i), the time-reversed matrix of rho is Y times the entrywise complex conjugate of rho times Y.

**Definition 1.3 (Purity plus overlap).**

$$\operatorname{purityPlusOverlap}\left(A, psi\right) = \operatorname{Re}\left(\operatorname{Tr}\left(\operatorname{reducedState}\left(A, psi\right) \cdot \operatorname{reducedState}\left(A, psi\right)\right) + \operatorname{Tr}\left(\operatorname{reducedState}\left(A, psi\right) \cdot \operatorname{timeReversed}\left(A, \operatorname{reducedState}\left(A, psi\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.purityPlusOverlap` (`✓ std3`).

*Citation.* Eduardo Serrano-Ensástiga; Olivier Giraud; John Martin (2026). *Multiqubit monogamy relations beyond shadow inequalities*. DOI: [10.1103/9fkf-hm8l](https://doi.org/10.1103/9fkf-hm8l). URL: <https://arxiv.org/abs/2507.12680v2>.

*Commentary.*

F_A(psi) is the real part of Tr(rho_A rho_A) + Tr(rho_A rho~_A), the sum of the purity of rho_A and the overlap R of rho_A with its time-reversed matrix.

**Definition 1.4 (The conjectured minimum).**

$$\operatorname{conjecturedMin}\left(N, k\right) = \operatorname{ite}\left(N < 2 \cdot k, \frac{2^{k}}{2^{N}}, \frac{2}{2^{k}}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.conjecturedMin` (`✓ std3`).

*Citation.* Eduardo Serrano-Ensástiga; Olivier Giraud; John Martin (2026). *Multiqubit monogamy relations beyond shadow inequalities*. DOI: [10.1103/9fkf-hm8l](https://doi.org/10.1103/9fkf-hm8l). URL: <https://arxiv.org/abs/2507.12680v2>.

*Commentary.*

m(N, k) is 2^k / 2^N when N < 2k and 2 / 2^k otherwise.

**Definition 1.5 (Conjecture 2).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N}, \forall A \subseteq \operatorname{Fin}\left(N\right), (1 \le \left|A\right|) \Rightarrow \left((\left|A\right| < N) \Rightarrow \left((\forall psi \in \mathbb{C}^{Conf}, (\sum_{w} \left|psi\left(w\right)\right|^{2} = 1) \Rightarrow \operatorname{conjecturedMin}\left(N, \left|A\right|\right) \le \operatorname{purityPlusOverlap}\left(A, psi\right)) \land (\exists psi \in \mathbb{C}^{Conf}, (\sum_{w} \left|psi\left(w\right)\right|^{2} = 1) \land (\operatorname{purityPlusOverlap}\left(A, psi\right) = \operatorname{conjecturedMin}\left(N, \left|A\right|\right)))\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.claim` (`✓ std3`).

*Citation.* Eduardo Serrano-Ensástiga; Olivier Giraud; John Martin (2026). *Multiqubit monogamy relations beyond shadow inequalities*. DOI: [10.1103/9fkf-hm8l](https://doi.org/10.1103/9fkf-hm8l). URL: <https://arxiv.org/abs/2507.12680v2>.

*Commentary.*

Write Conf for the set of configurations of the N qubits, the maps from Fin N to {0, 1}, so that a vector of amplitudes is an element psi of C^Conf. For every N and every set A of qubits among N with 1 <= |A| < N: every unit vector psi gives F_A(psi) >= m(N, |A|), and some unit vector attains equality.

**Theorem 1.6 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/serrano-ensastiga-2026-purity-time-reversal-overlap-minimum` (proved) by `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"serrano-ensastiga-2026-purity-time-reversal-overlap-minimum","declaration_gid":"D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eduardo Serrano-Ensástiga; Olivier Giraud; John Martin (2026). *Multiqubit monogamy relations beyond shadow inequalities*. DOI: [10.1103/9fkf-hm8l](https://doi.org/10.1103/9fkf-hm8l). URL: <https://arxiv.org/abs/2507.12680v2>.

*Commentary.*

Write d = 2^k and r = 2^(N-k), let M be the d x r matrix of amplitudes psi(x, z), so that rho_A = M M^H with trace 1, and let Phi = Y conj(M). The matrix Y is Hermitian and Y Y = 1, so the time-reversed matrix of rho_A is Phi Phi^H, its trace is 1, and Phi^H Phi is the entrywise conjugate of M^H M. First, Tr(rho_A rho~_A) = Tr((M^H Phi)(M^H Phi)^H) >= 0, and Tr(rho_A^2) = Tr((M^H M)^2) is the squared Frobenius norm of the r x r matrix M^H M, which is at least |Tr(M^H M)|^2 / r = 1/r by the Cauchy-Schwarz inequality on its diagonal. Second, for the Hermitian matrix S = rho_A + rho~_A the real part of Tr(S^2) equals 2 F_A(psi), and it is the squared Frobenius norm of S, which is at least |Tr S|^2 / d = 4/d. So F_A(psi) >= max(1/r, 2/d), which is m(N, k). If 2k <= N, choose an injection iota of A into the other qubits and let psi(x, z) = d^(-1/2) when z extends x along iota by zeros, and 0 otherwise; then rho_A and its time-reversed matrix are both the identity divided by d, and F_A(psi) = 2/d. If 2k > N, choose an injection kappa of the other qubits into A and a qubit i0 of A outside its image, and let psi(x, z) = r^(-1/2) when x extends z along kappa by zeros, and 0 otherwise; then M^H M is the identity divided by r, so Tr(rho_A^2) = 1/r, and every entry of M^H Phi contains the factor sigma_y(0, 0) = 0 at the qubit i0, so the overlap vanishes and F_A(psi) = 1/r.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.conjecturedMin`
- Truth anchor: `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.purityPlusOverlap`
- Truth anchor: `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.reducedState`
- Truth anchor: `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.timeReversed`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
