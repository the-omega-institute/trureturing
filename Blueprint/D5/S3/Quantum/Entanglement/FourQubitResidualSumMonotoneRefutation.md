# The residual-correlation sum of four qubits is not an entanglement monotone

## Abstract

Bai, Yang and Wang (arXiv:quant-ph/0703098, Phys. Rev. A 76, 022336) conjecture that the sum of the residual correlations M = sum_k tau_k - 2 sum_{p<q} C_pq^2 of a four-qubit pure state, built from the one-qubit linear entropies and Wootters' concurrences of the pairs, is an entanglement monotone. It is not: a two-outcome diagonal measurement on one qubit of the state (20|0001> + 2|1000> + 6|1011> + |1110>)/21 raises the average of M from 7552/194481 to 3528832/85766121.

**Definition 1.1 (Linear entropy).**

$$\forall k : \operatorname{Fin}\left(4\right), \forall \psi : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, \operatorname{linearEntropy}\left(k, \psi\right) = 2 \cdot (1 - \operatorname{ReTr}\left(\operatorname{reducedState}\left(\ \{k\ \}, \psi\right) \cdot \operatorname{reducedState}\left(\ \{k\ \}, \psi\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.linearEntropy` (`✓ std3`).

*Citation.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

For a four-qubit vector psi, a function from the configurations Fin 4 -> Fin 2 to the complex numbers with the qubits A, B, C, D at the indices 0, 1, 2, 3, the reduced state of the qubit k is the existing reducedState, the partial trace of the projector onto psi over the other three qubits. The linear entropy of the qubit k is tau_k = 2 (1 - Tr rho_k^2).

**Definition 1.2 (Concurrence of a pair).**

$$\forall p : \operatorname{Fin}\left(4\right), \forall q : \operatorname{Fin}\left(4\right), \forall \psi : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, \forall \rho : \operatorname{Matrix}\left((\ \{p, q\ \} \to \operatorname{Fin}\left(2\right)), (\ \{p, q\ \} \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall l : \operatorname{List}\left(\mathbb{R}\right), (\rho = \operatorname{reducedState}\left(\ \{p, q\ \}, \psi\right)) \Rightarrow ((l = \operatorname{sortDesc}\left(\operatorname{map}\left(\operatorname{re}, \operatorname{roots}\left(\operatorname{charpoly}\left(\rho \cdot \operatorname{timeReversed}\left(\ \{p, q\ \}, \rho\right)\right)\right)\right)\right)) \Rightarrow (\operatorname{concurrence}\left(p, q, \psi\right) = \max(\sqrt{\operatorname{getD}\left(l, 0, 0\right)} - \sqrt{\operatorname{getD}\left(l, 1, 0\right)} - \sqrt{\operatorname{getD}\left(l, 2, 0\right)} - \sqrt{\operatorname{getD}\left(l, 3, 0\right)}, 0)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.concurrence` (`✓ std3`).

*Citation.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

For two qubits p and q, rho is the reduced state of the pair {p, q} (the existing reducedState) and the existing timeReversed applies sigma_y to each qubit of the pair after complex conjugation, so that rho timeReversed(rho) is the matrix rho_pq (sigma_y x sigma_y) rho_pq^* (sigma_y x sigma_y) of Wootters' formula. The list l consists of the real parts of the roots of its characteristic polynomial, with multiplicity, sorted decreasingly; getD(l, i, 0) is its entry at position i, or 0 when the list is shorter. The concurrence is max(sqrt(l_0) - sqrt(l_1) - sqrt(l_2) - sqrt(l_3), 0); for p different from q the four entries are the eigenvalues lambda_1 >= lambda_2 >= lambda_3 >= lambda_4 of the paper.

**Definition 1.3 (The sum of the residual correlations).**

$$\forall \psi : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, \operatorname{residualSum}\left(\psi\right) = \sum_{k} \operatorname{linearEntropy}\left(k, \psi\right) - 2 \cdot \sum_{p<q} \operatorname{concurrence}\left(p, q, \psi\right)^{2}$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.residualSum` (`✓ std3`).

*Citation.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

Eq. (7) of the paper: M = sum_k tau_k - 2 sum_{p>q} C_pq^2 over the four qubits and the six pairs; each pair is counted once, here as p < q.

**Definition 1.4 (The conjectured monotonicity).**

$$(claim) \Leftrightarrow (\forall \psi : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}, (\sum_{w} \left\lVert \psi\left(w\right) \right\rVert^{2} = 1) \Rightarrow (\forall n : \mathbb{N}, \forall K : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), (\sum_{j} \left(K_{j}\right)^{H} \cdot K_{j} = 1) \Rightarrow (\forall p : \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall j : \operatorname{Fin}\left(n\right), p_{j} = \sum_{w} \left\lVert (\operatorname{localOp}\left(0, K_{j}\right) \cdot \psi)\left(w\right) \right\rVert^{2}) \Rightarrow (\sum_{j : p_{j} \neq 0} p_{j} \cdot \operatorname{residualSum}\left(\frac{1}{\sqrt{p_{j}}} \cdot (\operatorname{localOp}\left(0, K_{j}\right) \cdot \psi)\right) \le \operatorname{residualSum}\left(\psi\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.claim` (`✓ std3`).

*Citation.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

An entanglement monotone does not increase on average under LOCC. A complete instrument K_0, ..., K_{n-1} on qubit A, with sum_j K_j^dagger K_j = I, is a one-step LOCC protocol; K_j acts on qubit A (index 0) through the existing localOp, the product operator with factor K_j at qubit 0 and the identity elsewhere, applied to psi by matrix-vector multiplication: the outcome j occurs with probability p_j = ||K_j psi||^2 (the weights p of the display) and leaves the normalized state K_j psi / sqrt(p_j). The displayed statement asserts sum_j p_j M(K_j psi / sqrt(p_j)) <= M(psi) for every normalized four-qubit vector and every such instrument, omitting the outcomes with p_j = 0; it is a consequence of the conjecture that M is an entanglement monotone.

**Definition 1.5 (Coordinates of a pair).**

$$\forall p, q : \operatorname{Fin}\left(4\right), (p \ne q) \Rightarrow (\forall x : (\ \{p, q\ \} \to \operatorname{Fin}\left(2\right)), \operatorname{pairEquiv}\left(p, q, x\right) = (x\left(p\right), x\left(q\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.pairEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

For distinct qubits p and q, pairEquiv reads a configuration x of the pair {p, q} as the ordered pair (x(p), x(q)) in Fin 2 x Fin 2.

**Definition 1.6 (Coordinates outside a pair).**

$$\forall p, q, r, s : \operatorname{Fin}\left(4\right), (((\neg (r \in \ \{p, q\ \})) \land (\neg (s \in \ \{p, q\ \}))) \land ((r \ne s) \land (\forall i : \operatorname{Fin}\left(4\right), (\neg (i \in \ \{p, q\ \})) \Rightarrow (i = r \lor i = s)))) \Rightarrow (\forall z : (\operatorname{Outside}\left(\ \{p, q\ \}\right) \to \operatorname{Fin}\left(2\right)), \operatorname{outEquiv}\left(p, q, r, s, z\right) = (z\left(r\right), z\left(s\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.outEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

When the qubits r and s are exactly the two qubits outside {p, q}, outEquiv reads a configuration z of those qubits as (z(r), z(s)).

**Definition 1.7 (Coordinate of one qubit).**

$$\forall k : \operatorname{Fin}\left(4\right), \forall x : (\ \{k\ \} \to \operatorname{Fin}\left(2\right)), \operatorname{singleEquiv}\left(k, x\right) = x\left(k\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.singleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

singleEquiv reads a configuration x of the single qubit k as its value x(k) in Fin 2.

**Definition 1.8 (Coordinates outside one qubit).**

$$\forall k, r, s, t : \operatorname{Fin}\left(4\right), (((((\neg (r \in \ \{k\ \})) \land (\neg (s \in \ \{k\ \}))) \land (\neg (t \in \ \{k\ \}))) \land (((r \ne s) \land (r \ne t)) \land (s \ne t))) \land (\forall i : \operatorname{Fin}\left(4\right), (\neg (i \in \ \{k\ \})) \Rightarrow (\left(i = r \lor i = s\right) \lor i = t))) \Rightarrow (\forall z : (\operatorname{Outside}\left(\ \{k\ \}\right) \to \operatorname{Fin}\left(2\right)), \operatorname{out3Equiv}\left(k, r, s, t, z\right) = (z\left(r\right), z\left(s\right), z\left(t\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.out3Equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

When the qubits r, s and t are exactly the three qubits other than k, out3Equiv reads a configuration z of those qubits as (z(r), z(s), z(t)).

**Definition 1.9 (Coordinates of four qubits).**

$$\forall w : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right)), \operatorname{fourEquiv}\left(w\right) = (w\left(0\right), w\left(1\right), w\left(2\right), w\left(3\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.fourEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

fourEquiv reads a configuration w of the four qubits as (w(0), w(1), w(2), w(3)).

**Definition 1.10 (The counterexample state).**

$$\psi = \frac{1}{21} \cdot (20 \cdot |0001\rangle + 2 \cdot |1000\rangle + 6 \cdot |1011\rangle + |1110\rangle)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

The state is (20|0001> + 2|1000> + 6|1011> + |1110>)/21, with norm one since 400 + 4 + 36 + 1 = 441.

**Definition 1.11 (The measurement on qubit A).**

$$K_{0} = \operatorname{diag}\left(\frac{21}{29}, 0\right),\qquad K_{1} = \operatorname{diag}\left(\frac{20}{29}, 1\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.instrument` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

The two outcomes are K_0 = diag(21/29, 0) and K_1 = diag(20/29, 1) on qubit A, with K_0^dagger K_0 + K_1^dagger K_1 = I.

**Theorem 1.12 (The residual-correlation sum increases on average).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bai-2007-residual-sum-monotone` (refuted) by `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bai-2007-residual-sum-monotone","declaration_gid":"D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yan-Kui Bai; Dong Yang; Z. D. Wang (2007). *Multipartite quantum correlation and entanglement in four-qubit pure states*. DOI: [10.1103/PhysRevA.76.022336](https://doi.org/10.1103/PhysRevA.76.022336). URL: <https://arxiv.org/abs/quant-ph/0703098v2>.

*Commentary.*

The outcome K_0 has probability 400/841 and leaves the product state |0001>, so its M is zero. The outcome K_1 has probability 441/841 and leaves (400|0001> + 58|1000> + 174|1011> + 29|1110>)/441. Every two-qubit reduced state of the three states is a real X matrix, with diagonal u, v, r, s in the basis 00, 01, 10, 11, an entry w between 00 and 11 and an entry z between 01 and 10; after reindexing the reduced state and sigma_y x sigma_y to Fin 2 x Fin 2, which keeps the characteristic polynomial, the characteristic polynomial factors as (X^2 - 2(us + w^2)X + (us - w^2)^2)(X^2 - 2(vr + z^2)X + (vr - z^2)^2), with roots (sqrt(us) + |w|)^2, (sqrt(us) - |w|)^2, (sqrt(vr) + |z|)^2 and (sqrt(vr) - |z|)^2, and sorting them gives the concurrence. The concurrences of the pairs AB, AC, AD, BC, BD, CD are (0, 240, 80, 4, 12, 0)/441 for the state and (0, 139200, 46400, 3364, 10092, 0)/194481 for the second outcome; with the linear entropies, M of the state is 7552/194481 and M of the second outcome is 2967747712/37822859361. The average of M after the measurement is 3528832/85766121, which exceeds 7552/194481 by 198400/85766121.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.concurrence`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.fourEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.instrument`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.linearEntropy`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.out3Equiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.outEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.pairEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.psi`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.residualSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.singleEquiv`
- Dependency: [D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum](PurityTimeReversalOverlapMinimum.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
