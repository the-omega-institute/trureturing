# No perfect state transfer at time pi on rational paths with 2^k + 1 vertices

## Abstract

Kirkland, McLaren, Pereira, Plosker and Zhang (arXiv:1708.03283) conjecture that a weighted path on at least four vertices, with or without potentials, whose edge weights are all rational has no perfect state transfer between its end vertices at readout time pi, and prove it for n = 4 and for n congruent to 3 or 5 modulo 8. For every k >= 1 the statement holds for the paths on n = 2^k + 1 vertices, with arbitrary real potentials and in both directions; for k >= 3 these sizes are congruent to 1 modulo 8.

**Definition 1.1 (The weighted path Hamiltonian).**

$$\forall m \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \forall i \in \operatorname{Fin}\left(m + 1\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \operatorname{pathHamiltonian}\left(r, q\right)\left(i, j\right) = \text{if} i = j \text{then} q\left(i\right) \text{else} \text{if} i + 1 = j \text{then} r\left(i\right) \text{else} \text{if} j + 1 = i \text{then} r\left(j\right) \text{else} 0$$

*Formalization.* `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian` (`✓ std3`).

*Citation.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

The vertices are 0, ..., m and the edge {t, t + 1} carries the weight r t for t in Fin m. The matrix has the real potential q i at the diagonal entry (i, i), the weight r i at the entries (i, i + 1) and (i + 1, i), and zero elsewhere; all entries are real numbers cast to complex numbers. This is the tridiagonal adjacency matrix with potentials of the source, on m + 1 vertices.

**Definition 1.2 (Perfect state transfer).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall H \in \operatorname{Matrix}\left(V, V, \mathbb{C}\right),\; \forall t \in \mathbb{R},\; \forall a \in V,\; \forall b \in V,\; \operatorname{HasPST}\left(H, t, a, b\right) \Leftrightarrow (\operatorname{normSq}\left(\operatorname{hamiltonianPropagator}\left(H, -t, a, b\right)\right) = 1)$$

*Formalization.* `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.HasPST` (`✓ std3`).

*Citation.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

Perfect state transfer from vertex a to vertex b at time t means |e_a^T exp(i t H) e_b|^2 = 1, where exp is the matrix exponential and normSq is the squared modulus of a complex number. The formal statement writes exp(i t H) as the repository propagator hamiltonianPropagator H s = exp(-i s H) at s = -t.

**Theorem 1.3 (Transfer from the first vertex forces mirror-symmetric weights).**

$$\forall m \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; (\forall t \in \operatorname{Fin}\left(m\right),\; 0 < r\left(t\right)) \Rightarrow (\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m + 1\right), \operatorname{Fin}\left(m + 1\right), \mathbb{C}\right),\; U^{*} \cdot U = 1 \Rightarrow (U \cdot \operatorname{pathHamiltonian}\left(r, q\right) = \operatorname{pathHamiltonian}\left(r, q\right) \cdot U \Rightarrow (\forall gamma \in \mathbb{C},\; \operatorname{normSq}\left(gamma\right) = 1 \Rightarrow ((\forall x \in \operatorname{Fin}\left(m + 1\right),\; U\left(x, 0\right) = \text{if} x = \operatorname{last}\left(m\right) \text{then} gamma \text{else} 0) \Rightarrow (\forall t \in \operatorname{Fin}\left(m\right),\; r\left(t\right) = r\left(\operatorname{rev}\left(t\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.persymmetric_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be unitary, commute with the path Hamiltonian H, and send the first basis vector to gamma times the last one, with |gamma| = 1. By induction on j, U e_j = gamma e_(m - j) and r t = r (m - 1 - t) for t < j. Indeed r_j U e_(j+1) = U(H e_j - q_j e_j - r_(j-1) e_(j-1)) = gamma (H e_(m-j) - q_j e_(m-j) - r_(j-1) e_(m-j+1)); by the induction hypothesis only the components at m - j - 1 and m - j remain, orthogonality of the columns j and j + 1 of U removes the second one, and the unit norm of column j + 1 together with the positivity of the weights gives r j = r (m - 1 - j). Here rev t is the mirror index m - 1 - t of the edge t, and last(m) is the vertex m.

**Theorem 1.4 (Spectral parity classes of a transfer at time pi).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall H \in \operatorname{Matrix}\left(V, V, \mathbb{C}\right),\; \operatorname{IsHermitian}\left(H\right) \Rightarrow (\forall a \in V,\; \forall b \in V,\; a \ne b \Rightarrow (\forall m \in \mathbb{N},\; \operatorname{card}\left(V\right) = m + 1 \Rightarrow (\forall P \in \mathbb{R},\; P \ne 0 \Rightarrow ((\forall p \in \mathbb{N},\; p \le m \Rightarrow (\left(H^{p}\right)\left(a, b\right) = \text{if} p = m \text{then} P \text{else} 0)) \Rightarrow (\operatorname{HasPST}\left(H, \pi, a, b\right) \Rightarrow (\exists z \in V \to \mathbb{Z},\; \exists A \in \operatorname{Finset}\left(V\right),\; \operatorname{Injective}\left(z\right) \land \left(\operatorname{Nonempty}\left(A\right) \land \left(A \ne \operatorname{univ} \land \left(\left(\forall i \in A,\; \operatorname{Even}\left(z\left(i\right)\right)\right) \land \left(\left(\forall i \in V,\; \left(\neg (i \in A)\right) \Rightarrow (\operatorname{Odd}\left(z\left(i\right)\right))\right) \land P \cdot \sum_{i \in A} (\prod_{j \in \operatorname{erase}\left(\operatorname{univ}, i\right)} ((z\left(i\right) - z\left(j\right) : \mathbb{Z}) : \mathbb{R}))^{-1} = \frac{1}{2}\right)\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pst_parity_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c k = W a k conj(W b k) for the orthonormal eigenvectors W of H with eigenvalues lambda k. The hypotheses on the powers of H give sum_k c k lambda_k^p = 0 for p < m and = P for p = m; evaluating sum_k c k f(lambda k) on the monic polynomial f = prod_{l != k} (X - lambda l) gives c k prod_{l != k} (lambda k - lambda l) = P, so the eigenvalues are distinct and every c k is a nonzero real number. Transfer at time pi forces exp(i pi lambda_k) conj(W b k) = gamma conj(W a k) with gamma = exp(i pi H)(a, b), since the sum of the squared moduli of their differences vanishes. Hence |c k| = |W a k|^2, whose sum is 1, while sum_k c k = 0. The class A of indices with c k > 0 has sum_{k in A} c k = 1/2, and exp(i pi lambda_k) equals gamma on A and -gamma off A. Shifting the eigenvalues by an eigenvalue of the class A gives integers z, even on A and odd off A, with lambda k - lambda l = z k - z l.

**Definition 1.5 (The rational weights statement on 2^k + 1 vertices).**

$$claim \Leftrightarrow (\forall k \in \mathbb{N},\; 1 \le k \Rightarrow (\forall r \in \operatorname{Fin}\left(2^{k}\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2^{k} + 1\right) \to \mathbb{R},\; (\forall j \in \operatorname{Fin}\left(2^{k}\right),\; \exists x \in \mathbb{Q},\; r\left(j\right) = x) \Rightarrow ((\forall j \in \operatorname{Fin}\left(2^{k}\right),\; 0 < r\left(j\right)) \Rightarrow (\left(\neg \operatorname{HasPST}\left(\operatorname{pathHamiltonian}\left(r, q\right), \pi, 0, \operatorname{last}\left(2^{k}\right)\right)\right) \land \left(\neg \operatorname{HasPST}\left(\operatorname{pathHamiltonian}\left(r, q\right), \pi, \operatorname{last}\left(2^{k}\right), 0\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

For k >= 1 and the path on n = 2^k + 1 vertices with edge weights r in Fin(2^k) -> R and potentials q in Fin(2^k + 1) -> R: if every weight is rational and positive, there is no perfect state transfer at time pi from the first vertex 0 to the last vertex 2^k, nor from the last vertex to the first. The rationality hypothesis is written as the existence of a rational number equal to each weight. The source states its conjecture for all n >= 4 and does not single out this family; the statement is the restriction of that conjecture to the sizes n = 2^k + 1, with k = 1 added.

**Theorem 1.6 (Rational paths on 2^k + 1 vertices have no transfer at time pi).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

The propagator exp(i pi H) is symmetric, so both directions reduce to transfer from the last vertex to the first. The entries of H^p in the column of the first vertex vanish beyond distance p, and the entry at the last vertex of H^m is P = prod_t r t with m = 2^k. The spectral parity classes give integers z, even on a class A and odd off A, with P sum_{i in A} 1 / prod_{j != i} (z i - z j) = 1/2, and A is neither empty nor everything. The column of the propagator at the first vertex is gamma times the last basis vector, so the weights are mirror symmetric and P is the square Q^2 of a rational number Q. Since C(2^k - 1, j) is odd for every j < 2^k, the partial divided-difference sum over A has 2-adic valuation 0. Then 2 v_2(Q) = v_2(1/2) = -1, which is impossible. This is partial progress on the conjecture of the source: k = 1 gives n = 3, below the range n >= 4 of the conjecture; k = 2 gives n = 5, one of the cases proved in the source; the new sizes are those with k >= 3, namely n = 9, 17, 33, ...; the other sizes are not addressed.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.HasPST`
- Truth anchor: `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian`
- Truth anchor: `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.persymmetric_weights`
- Truth anchor: `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pst_parity_classes`
- Truth anchor: `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.result`
- Dependency: [D5/S3/Quantum/Dynamics/ParityNodeDividedDifference](ParityNodeDividedDifference.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
