# Middle-vertex spectral weights and integer moments of odd paths with end transfer at time pi

## Abstract

Let H be the Hamiltonian of a weighted path on the 2m + 1 vertices 0, ..., 2m, with positive edge weights and real potentials, whose propagator exp(i pi H) has the entry 1 at the last and first vertices. Then H is invariant under the reversal of the vertices, its eigenvalues are distinct integers that are even on a class A of m + 1 indices and odd on the other m, the eigenvectors of the odd class vanish at the middle vertex c = m, and the eigenvector of index k in A has squared modulus prod_{l not in A} (z k - z l) / prod_{l in A, l != k} (z k - z l) at c. The diagonal entries (H^p)(c, c) are integers congruent to the binomial coefficients C(m, p) modulo 2.

**Theorem 1.1 (Transfer with phase one makes the Hamiltonian reversal invariant).**

$$\forall m \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(2 \cdot m\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot m + 1\right) \to \mathbb{R},\; (\forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; 0 < r\left(t\right)) \Rightarrow (\operatorname{hamiltonianPropagator}\left(\operatorname{pathHamiltonian}\left(r, q\right), -\pi, \operatorname{last}\left(2 \cdot m\right), 0\right) = 1 \Rightarrow (\forall x \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \forall y \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \operatorname{pathHamiltonian}\left(r, q\right)\left(\operatorname{rev}\left(x\right), \operatorname{rev}\left(y\right)\right) = \operatorname{pathHamiltonian}\left(r, q\right)\left(x, y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.reversal_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

The hypothesis says that the entry of exp(i pi H) at the last and first vertices equals 1; hamiltonianPropagator H s = exp(-i s H) is the repository propagator, taken at s = -pi. This entry has modulus one, so the column of the first vertex of the unitary matrix exp(i pi H) is the last basis vector, and the reversal form of a unitary commuting with the path Hamiltonian gives exp(i pi H) e_i = e_(2m - i) for every vertex i: the propagator is the reversal permutation matrix R. Since H commutes with exp(i pi H), comparing the entries of R H and H R at (x, rev y) gives H(rev x, rev y) = H(x, y), where rev x = 2m - x and last(2m) is the vertex 2m. The source records the underlying fact as known, citing Kay: a symmetric tridiagonal Hamiltonian with perfect state transfer between its end vertices is persymmetric. The statement here is its form for the path Hamiltonian with positive weights and transfer phase one, for the potentials as well as the weights.

**Theorem 1.2 (Spectral weights at the middle vertex).**

$$\forall m \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(2 \cdot m\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot m + 1\right) \to \mathbb{R},\; \operatorname{IsHermitian}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right) \Rightarrow ((\forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; 0 < r\left(t\right)) \Rightarrow (\operatorname{hamiltonianPropagator}\left(\operatorname{pathHamiltonian}\left(r, q\right), -\pi, \operatorname{last}\left(2 \cdot m\right), 0\right) = 1 \Rightarrow (\forall c \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; (c : \mathbb{N}) = m \Rightarrow (\exists z \in \operatorname{Fin}\left(2 \cdot m + 1\right) \to \mathbb{Z},\; \exists A \in \operatorname{Finset}\left(\operatorname{Fin}\left(2 \cdot m + 1\right)\right),\; \operatorname{Injective}\left(z\right) \land \left(\operatorname{card}\left(A\right) = m + 1 \land \left((\forall k \in A,\; \operatorname{Even}\left(z\left(k\right)\right)) \land \left((\forall k \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \left(\neg (k \in A)\right) \Rightarrow (\operatorname{Odd}\left(z\left(k\right)\right))) \land \left((\forall k \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \operatorname{eigenvalues}\left(\operatorname{pathHamiltonian}\left(r, q\right), k\right) = (z\left(k\right) : \mathbb{R})) \land \left((\forall k \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \left(\neg (k \in A)\right) \Rightarrow (\operatorname{eigenvectorUnitary}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right)\left(c, k\right) = 0)) \land (\forall k \in A,\; \operatorname{normSq}\left(\operatorname{eigenvectorUnitary}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right)\left(c, k\right)\right) = \frac{\prod_{l \in \operatorname{compl}\left(A\right)} ((z\left(k\right) - z\left(l\right) : \mathbb{Z}) : \mathbb{R})}{\prod_{l \in \operatorname{erase}\left(A, k\right)} ((z\left(k\right) - z\left(l\right) : \mathbb{Z}) : \mathbb{R})})\right)\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.middle_vertex_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

Let W be the unitary matrix of orthonormal eigenvectors of H and lambda k its eigenvalues, and write E k = exp(i pi lambda_k). The spectral form of exp(i pi H) = R gives W(rev x, k) = E k W(x, k); applying it twice to a nonzero entry of the column k gives (E k)^2 = 1. Let A be the set of indices with E k = 1. Then lambda_k is an even integer for k in A and an odd integer otherwise, and W(c, k) = 0 for k outside A because the middle vertex c is fixed by the reversal. The trace of R is 1, since c is its only fixed vertex, and it equals the sum of the E k, so #A - #A^c = 1 and #A = m + 1. The entries of H^p at the last and first vertices vanish for p < 2m and equal the product of all the weights for p = 2m; by the mirror symmetry of the weights this product is rho^2 with rho = r 0 r 1 ... r (m - 1). The entries of H^p at the middle and first vertices vanish for p < m and equal rho for p = m, and only the indices of A contribute to them. Evaluating these moment relations on nodal polynomials gives |W(0, k)|^2 prod_{l != k} (lambda_k - lambda_l) = rho^2 and W(c, k) conj(W(0, k)) prod_{l in A, l != k} (lambda_k - lambda_l) = rho for k in A. In particular the eigenvalues are distinct, and dividing the squared modulus of the second relation by the first gives the stated formula. In the formal statement eigenvalues and eigenvectorUnitary are the eigenvalues and the eigenvector matrix attached to the Hermitian matrix H, and the middle vertex is a vertex c whose value is m. The source records as known that the eigenvectors of a mirror-symmetric Hamiltonian are symmetric or antisymmetric, citing Cantoni and Butler, and that after a common shift the eigenvalues of a path with perfect state transfer at time pi between its end vertices are integers that alternate between even and odd. The count #A = m + 1 and the formula for the squared modulus at the middle vertex are derived here.

**Theorem 1.3 (Integer moments at the middle vertex and their parity).**

$$\forall m \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(2 \cdot m\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot m + 1\right) \to \mathbb{R},\; (\forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; 0 < r\left(t\right)) \Rightarrow (\operatorname{hamiltonianPropagator}\left(\operatorname{pathHamiltonian}\left(r, q\right), -\pi, \operatorname{last}\left(2 \cdot m\right), 0\right) = 1 \Rightarrow (\forall c \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; (c : \mathbb{N}) = m \Rightarrow (\exists mu \in \mathbb{N} \to \mathbb{Z},\; (\forall p \in \mathbb{N},\; \left(\operatorname{pathHamiltonian}\left(r, q\right)^{p}\right)\left(c, c\right) = (mu\left(p\right) : \mathbb{C})) \land (\forall p \in \mathbb{N},\; (mu\left(p\right) : \operatorname{ZMod}\left(2\right)) = (\operatorname{choose}\left(m, p\right) : \operatorname{ZMod}\left(2\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.middle_vertex_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

By the spectral theorem (H^p)(c, c) = sum_k |W(c, k)|^2 lambda_k^p, and by the spectral weights at the middle vertex this is the sum over k in A of z_k^p P_B(z k) / prod_{l in A, l != k} (z k - z l), where P_A and P_B are the monic integer polynomials whose roots are the eigenvalues of the even class A and of the odd class. By the Lagrange coefficient formula over the m + 1 nodes of A, this sum is the coefficient of X^m in the remainder of X^p P_B modulo P_A, which is an integer mu p. Modulo 2 the polynomial P_A becomes X^(m+1) and P_B becomes (X + 1)^m, so mu p is congruent to the coefficient of X^m in X^p (X + 1)^m, which is C(m, m - p) = C(m, p) for p <= m and 0 = C(m, p) for p > m. In the formal statement the congruence is the equality of the images of mu p and of C(m, p) in the integers modulo 2. For p = 1 the moment is the potential at the middle vertex, which the source expresses as the alternating sum of the eigenvalues in its corollary on middle weights.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.middle_vertex_moments`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.middle_vertex_weights`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.reversal_symmetric`
- Dependency: [D5/S3/Quantum/Dynamics/RationalWeightPathTransfer](RationalWeightPathTransfer.md)
