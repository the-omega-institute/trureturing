# Middle-edge spectral weights, integer moments and Gram identity of even paths with end transfer at time pi

## Abstract

Let H be the Hamiltonian of a weighted path on the 2k + 2 vertices 0, ..., 2k + 1, with positive edge weights and real potentials, whose propagator exp(i pi H) has the entry 1 at the last and first vertices. Then the eigenvalues of H are distinct integers that are even on a class A of k + 1 indices and odd on the other k + 1, the eigenvectors of the odd class have opposite entries at the two middle vertices a = k and b = k + 1, and the eigenvector of index j in A satisfies |W(a, j) + W(b, j)|^2 = prod_{l not in A} (z j - z l) / (rho prod_{l in A, l != j} (z j - z l)), where rho is the weight of the middle edge. With S p the sum of the four entries of H^p at a and b, the number rho S p is the integer coefficient of X^k in the remainder of X^p P_B modulo P_A, for the nodal polynomials P_A and P_B of the two classes, and S 0 S 2 - (S 1)^2 = 4 r'^2 for the weight r' of the edge following the middle edge.

**Definition 1.1 (The moment of a matrix at the sum of two basis vectors).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall H \in \operatorname{Matrix}\left(V, V, \mathbb{C}\right),\; \forall a \in V,\; \forall b \in V,\; \forall p \in \mathbb{N},\; \operatorname{pairMoment}\left(H, a, b, p\right) = \left(H^{p}\right)\left(a, a\right) + \left(H^{p}\right)\left(a, b\right) + \left(H^{p}\right)\left(b, a\right) + \left(H^{p}\right)\left(b, b\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.pairMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

For a square complex matrix H indexed by a finite type V and two indices a and b, the moment of order p at the vector f = e_a + e_b is f^T H^p f, the sum of the four entries of H^p at the indices a and b. For a real symmetric matrix H it is the moment of order p of the spectral measure of H at f. It is used for the path Hamiltonian at the two ends of the middle edge of a path with an even number of vertices.

**Definition 1.2 (The nodal moments of one finite set of integer nodes against another).**

$$\forall iota \in Type,\; \forall z \in iota \to \mathbb{Z},\; \forall A \in \operatorname{Finset}\left(iota\right),\; \forall B \in \operatorname{Finset}\left(iota\right),\; \forall k \in \mathbb{N},\; \forall p \in \mathbb{N},\; \operatorname{nodalMoment}\left(z, A, B, k, p\right) = \operatorname{coeff}\left(\operatorname{modByMonic}\left(X^{p} \cdot \prod_{l \in B} (X - \operatorname{C}\left(z\left(l\right)\right)), \prod_{l \in A} (X - \operatorname{C}\left(z\left(l\right)\right))\right), k\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.nodalMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

For integers z indexed by a type iota and finite sets A and B of indices, let P_A and P_B be the monic polynomials with the roots z l, l in A, and z l, l in B. The nodal moment of order p and degree k is the coefficient of X^k in the remainder of X^p P_B modulo P_A, an integer. In the formal statement modByMonic is the remainder of the division by a monic polynomial, coeff extracts a coefficient, and C embeds the integers into the integer polynomials. When A has k + 1 elements and the nodes of A are distinct, the Lagrange coefficient formula identifies it with the divided difference sum over j in A of z_j^p P_B(z j) / prod_{l in A, l != j} (z j - z l).

**Theorem 1.3 (Spectral weights at the middle edge).**

$$\forall k \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(2 \cdot k + 1\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right) \to \mathbb{R},\; \operatorname{IsHermitian}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right) \Rightarrow ((\forall t \in \operatorname{Fin}\left(2 \cdot k + 1\right),\; 0 < r\left(t\right)) \Rightarrow (\operatorname{hamiltonianPropagator}\left(\operatorname{pathHamiltonian}\left(r, q\right), -\pi, \operatorname{last}\left(2 \cdot k + 1\right), 0\right) = 1 \Rightarrow (\forall a \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \forall b \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; (a : \mathbb{N}) = k \Rightarrow ((b : \mathbb{N}) = k + 1 \Rightarrow (\forall e \in \operatorname{Fin}\left(2 \cdot k + 1\right),\; (e : \mathbb{N}) = k \Rightarrow (\exists z \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right) \to \mathbb{Z},\; \exists A \in \operatorname{Finset}\left(\operatorname{Fin}\left(2 \cdot k + 1 + 1\right)\right),\; \operatorname{Injective}\left(z\right) \land \left(\operatorname{card}\left(A\right) = k + 1 \land \left((\forall j \in A,\; \operatorname{Even}\left(z\left(j\right)\right)) \land \left((\forall j \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \left(\neg (j \in A)\right) \Rightarrow (\operatorname{Odd}\left(z\left(j\right)\right))) \land \left((\forall j \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \operatorname{eigenvalues}\left(\operatorname{pathHamiltonian}\left(r, q\right), j\right) = (z\left(j\right) : \mathbb{R})) \land \left((\forall j \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \left(\neg (j \in A)\right) \Rightarrow (\operatorname{eigenvectorUnitary}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right)\left(a, j\right) + \operatorname{eigenvectorUnitary}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right)\left(b, j\right) = 0)) \land (\forall j \in A,\; \operatorname{normSq}\left(\operatorname{eigenvectorUnitary}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right)\left(a, j\right) + \operatorname{eigenvectorUnitary}\left(\operatorname{pathHamiltonian}\left(r, q\right)\right)\left(b, j\right)\right) = \frac{\prod_{l \in \operatorname{compl}\left(A\right)} ((z\left(j\right) - z\left(l\right) : \mathbb{Z}) : \mathbb{R})}{r\left(e\right) \cdot \prod_{l \in \operatorname{erase}\left(A, j\right)} ((z\left(j\right) - z\left(l\right) : \mathbb{Z}) : \mathbb{R})})\right)\right)\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

Let W be the unitary matrix of orthonormal eigenvectors of H and lambda k its eigenvalues. The reversal sign classes of the spectrum of a path with transfer of phase one give distinct integers z with lambda k = z k, even on a class A and odd off A, with W(rev x, k) = W(x, k) for k in A and W(rev x, k) = -W(x, k) otherwise, with #A - #A^c equal to the number of vertices fixed by the reversal, and with |W(0, j)|^2 prod_{l != j} (z j - z l) equal to the product of all the weights for j in A. The reversal rev x = 2k + 1 - x has no fixed vertex, so #A = #A^c = k + 1; it exchanges the middle vertices a = k and b = k + 1, so W(a, j) + W(b, j) = 0 for j outside A. By the mirror symmetry of the weights, the product of all the weights is rho Q^2, where rho = r(k) is the weight of the middle edge e and Q = r(0) r(1) ... r(k - 1). The entries of H^p at a and the first vertex vanish for p < k and equal Q for p = k, and the entries at b and the first vertex vanish for p <= k; only the indices of A contribute to the sum of the two, so evaluating these moment relations on nodal polynomials gives (W(a, j) + W(b, j)) conj(W(0, j)) prod_{l in A, l != j} (z j - z l) = Q for j in A. Dividing the squared modulus of this relation by the relation at the first vertex gives the stated formula. In the formal statement eigenvalues and eigenvectorUnitary are the eigenvalues and the eigenvector matrix attached to the Hermitian matrix H, hamiltonianPropagator H s = exp(-i s H) is the repository propagator taken at s = -pi, last(2k + 1) is the vertex 2k + 1, and a, b, e are a vertex of value k, a vertex of value k + 1 and an edge of value k. The source records as known that the eigenvectors of a mirror-symmetric Hamiltonian are symmetric or antisymmetric, citing Cantoni and Butler, and that after a common shift the eigenvalues of a path with perfect state transfer at time pi between its end vertices are integers that alternate between even and odd. The count #A = k + 1 and the formula for the squared modulus at the middle edge are derived here.

**Theorem 1.4 (Integer moments at the middle edge).**

$$\forall k \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(2 \cdot k + 1\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right) \to \mathbb{R},\; (\forall t \in \operatorname{Fin}\left(2 \cdot k + 1\right),\; 0 < r\left(t\right)) \Rightarrow (\operatorname{hamiltonianPropagator}\left(\operatorname{pathHamiltonian}\left(r, q\right), -\pi, \operatorname{last}\left(2 \cdot k + 1\right), 0\right) = 1 \Rightarrow (\forall a \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \forall b \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; (a : \mathbb{N}) = k \Rightarrow ((b : \mathbb{N}) = k + 1 \Rightarrow (\forall e \in \operatorname{Fin}\left(2 \cdot k + 1\right),\; (e : \mathbb{N}) = k \Rightarrow (\exists z \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right) \to \mathbb{Z},\; \exists A \in \operatorname{Finset}\left(\operatorname{Fin}\left(2 \cdot k + 1 + 1\right)\right),\; \operatorname{card}\left(A\right) = k + 1 \land \left(\operatorname{card}\left(\operatorname{compl}\left(A\right)\right) = k + 1 \land \left((\forall j \in A,\; \operatorname{Even}\left(z\left(j\right)\right)) \land \left((\forall j \in \operatorname{compl}\left(A\right),\; \operatorname{Odd}\left(z\left(j\right)\right)) \land (\forall p \in \mathbb{N},\; (r\left(e\right) : \mathbb{C}) \cdot \operatorname{pairMoment}\left(\operatorname{pathHamiltonian}\left(r, q\right), a, b, p\right) = ((\operatorname{nodalMoment}\left(z, A, \operatorname{compl}\left(A\right), k, p\right) : \mathbb{Z}) : \mathbb{C}))\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

By the spectral theorem the moment S p of H^p at e_a + e_b is the sum over the eigenvector indices j of lambda_j^p |W(a, j) + W(b, j)|^2. The indices outside A do not contribute, and by the spectral weights at the middle edge rho S p is the sum over j in A of z_j^p P_B(z j) / prod_{l in A, l != j} (z j - z l), where P_A and P_B are the monic integer polynomials whose roots are the eigenvalues of the even class A and of the odd class. By the Lagrange coefficient formula over the k + 1 nodes of A, this sum is the coefficient of X^k in the remainder of X^p P_B modulo P_A, the nodal moment of order p of A against its complement. In the formal statement the equality holds between complex numbers, the weight rho = r e and the integer nodal moment being cast. For p = 0 the remainder is P_B - P_A and S 0 = 2, so 2 rho is the sum of the eigenvalues of the even class minus the sum of those of the odd class. The source's corollary on middle weights gives the middle weight of a mirror-symmetric path with an even number of vertices as S_1 / 2, where S_1 is the alternating sum of the ordered eigenvalues; the integrality of rho S p for every p is derived here.

**Theorem 1.5 (Gram identity of the middle-edge moments).**

$$\forall k \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(2 \cdot k + 1\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right) \to \mathbb{R},\; (\forall x \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \forall y \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \operatorname{pathHamiltonian}\left(r, q\right)\left(\operatorname{rev}\left(x\right), \operatorname{rev}\left(y\right)\right) = \operatorname{pathHamiltonian}\left(r, q\right)\left(x, y\right)) \Rightarrow (\forall a \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; \forall b \in \operatorname{Fin}\left(2 \cdot k + 1 + 1\right),\; (a : \mathbb{N}) = k \Rightarrow ((b : \mathbb{N}) = k + 1 \Rightarrow (\forall f \in \operatorname{Fin}\left(2 \cdot k + 1\right),\; (f : \mathbb{N}) = k + 1 \Rightarrow (\operatorname{pairMoment}\left(\operatorname{pathHamiltonian}\left(r, q\right), a, b, 0\right) \cdot \operatorname{pairMoment}\left(\operatorname{pathHamiltonian}\left(r, q\right), a, b, 2\right) - \operatorname{pairMoment}\left(\operatorname{pathHamiltonian}\left(r, q\right), a, b, 1\right)^{2} = 4 \cdot (r\left(f\right) : \mathbb{C})^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

Let H be the path Hamiltonian on the vertices 0, ..., 2k + 1, invariant under the reversal rev x = 2k + 1 - x, and let f be the edge following the middle edge, so that k >= 1. Write S p for the moment of H^p at e_a + e_b, with a = k and b = k + 1 the ends of the middle edge, and v(x) = H(x, a) + H(x, b) for the column of H at e_a + e_b. Since H is real symmetric, S 0 = 2, S 1 = v(a) + v(b) and S 2 = sum_x v(x)^2. The column v is invariant under the reversal, vanishes outside the four vertices k - 1, k, k + 1, k + 2, and its entry at the vertex k + 2 is the weight r(k + 1) of the edge f. Hence S 1 = 2 v(a), S 2 = 2 v(a)^2 + 2 r(k + 1)^2 and S 0 S 2 - (S 1)^2 = 4 r(k + 1)^2. In the formal statement the weight r f is cast to a complex number. The identity is the expression of the second Hankel determinant of the moments of a Jacobi matrix by its first off-diagonal entry, for the block acting on the reversal-invariant vectors, whose first off-diagonal entry is the weight next to the middle edge; it is derived here directly for the path Hamiltonian. For n = 4 the source computes the weight next to the middle edge from the eigenvalues and shows that it is irrational.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_gram`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_moments`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_weights`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.nodalMoment`
- Truth anchor: `D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.pairMoment`
- Dependency: [D5/S3/Quantum/Dynamics/PathMiddleVertexMoments](PathMiddleVertexMoments.md)
