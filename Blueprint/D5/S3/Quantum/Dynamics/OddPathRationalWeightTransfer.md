# No perfect state transfer at time pi on rational paths with an odd number of vertices

## Abstract

Kirkland, McLaren, Pereira, Plosker and Zhang (arXiv:1708.03283) conjecture that a weighted path on at least four vertices, with or without potentials, whose edge weights are all rational has no perfect state transfer between its end vertices at readout time pi, and prove it for n = 4 and for n congruent to 3 or 5 modulo 8. The statement holds for every odd number of vertices n = 2m + 1 with m >= 1, with arbitrary real potentials and in both directions. The conjecture is not settled for the even sizes n >= 6.

**Theorem 1.1 (Gram determinant of the middle-vertex moments).**

$$\forall m \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(2 \cdot m\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot m + 1\right) \to \mathbb{R},\; (\forall x \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \forall y \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; \operatorname{pathHamiltonian}\left(r, q\right)\left(\operatorname{rev}\left(x\right), \operatorname{rev}\left(y\right)\right) = \operatorname{pathHamiltonian}\left(r, q\right)\left(x, y\right)) \Rightarrow (\forall c \in \operatorname{Fin}\left(2 \cdot m + 1\right),\; (c : \mathbb{N}) = m \Rightarrow (\forall j \in \mathbb{N},\; j \le m \Rightarrow (\operatorname{det}_{a, b \in \operatorname{Fin}\left(j + 1\right)} \left(\operatorname{pathHamiltonian}\left(r, q\right)^{a + b}\right)\left(c, c\right) = 2^{j} \cdot (\prod_{a \in \operatorname{Fin}\left(j + 1\right)} \prod_{t \in \operatorname{Fin}\left(a\right)} (r\left(m + t\right) : \mathbb{C}))^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.middle_moment_gram_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

Let H be the path Hamiltonian on the vertices 0, ..., 2m, invariant under the reversal rev x = 2m - x, and let c be the middle vertex m. Since H is real symmetric, (H^(a+b))(c, c) = sum_i (H^a)(i, c) (H^b)(i, c). The column of H^a at c is invariant under the reversal, vanishes at the vertices at distance more than a from c, and its entry at the vertex m + a is the product w_a = r(m) r(m + 1) ... r(m + a - 1) of the a edge weights following c. Pairing each vertex below c with its mirror image gives (H^(a+b))(c, c) = T(a, 0) T(b, 0) + 2 sum_{d >= 1} T(a, d) T(b, d) with T(a, d) = (H^a)(m + d, c). For a, d <= j the matrix T is lower triangular with diagonal entries w_a, so the Hankel matrix of the moments is T diag(1, 2, ..., 2) T^T and its determinant is 2^j (w_0 w_1 ... w_j)^2. In the formal statement the matrix is indexed by a, b in Fin(j + 1), and r(m + t), for t < a <= j <= m, is the weight of the edge {m + t, m + t + 1} cast to a complex number. The source obtains the weight next to the middle vertex of a mirror-symmetric path with an odd number of vertices from the eigenvalues, through the orthogonal similarity of Cantoni and Butler between a mirror-symmetric matrix and a direct sum of two blocks of about half the size; the case j = 1 of the identity, (H^2)(c, c) - (H(c, c))^2 = 2 r(m)^2, expresses the same weight by the first two moments at the middle vertex. The identity is the expression of the Hankel determinants of the moments of a Jacobi matrix by its off-diagonal entries, for the block acting on the reversal-invariant vectors, whose first off-diagonal entry is sqrt(2) r(m); it is derived here directly for the path Hamiltonian.

**Definition 1.2 (The rational weights statement on an odd number of vertices).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; 1 \le m \Rightarrow (\forall r \in \operatorname{Fin}\left(2 \cdot m\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot m + 1\right) \to \mathbb{R},\; (\forall j \in \operatorname{Fin}\left(2 \cdot m\right),\; \exists x \in \mathbb{Q},\; r\left(j\right) = x) \Rightarrow ((\forall j \in \operatorname{Fin}\left(2 \cdot m\right),\; 0 < r\left(j\right)) \Rightarrow (\left(\neg \operatorname{HasPST}\left(\operatorname{pathHamiltonian}\left(r, q\right), \pi, 0, \operatorname{last}\left(2 \cdot m\right)\right)\right) \land \left(\neg \operatorname{HasPST}\left(\operatorname{pathHamiltonian}\left(r, q\right), \pi, \operatorname{last}\left(2 \cdot m\right), 0\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

For m >= 1 and the path on n = 2m + 1 vertices with edge weights r in Fin(2m) -> R and potentials q in Fin(2m + 1) -> R: if every weight is rational and positive, there is no perfect state transfer at time pi from the first vertex 0 to the last vertex 2m, nor from the last vertex to the first. The rationality hypothesis is written as the existence of a rational number equal to each weight. The source states its conjecture for all n >= 4; the statement is the restriction of that conjecture to the odd sizes, with n = 3 added.

**Theorem 1.3 (Rational paths with an odd number of vertices have no transfer at time pi).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

The propagator exp(i pi H) is symmetric, so both directions reduce to transfer from the last vertex to the first. If the entry gamma of exp(i pi H) at the last and first vertices has modulus one, write gamma = exp(i pi theta) with theta real; subtracting theta from every potential keeps the weights and multiplies the propagator by exp(-i pi theta), so one may assume gamma = 1. Then H is invariant under the reversal, and the moments (H^p)(c, c) at the middle vertex c = m are integers mu p congruent to C(m, p) modulo 2. For j <= m the integer Hankel determinant D_j = det [mu(a + b)], a, b <= j, equals 2^j Q^2, where Q is the product over a <= j of the products of the a weights following c, a nonzero rational number. Modulo 2 the matrix is [C(m, a + b)]. If m is odd, take j = m: the entries with a + b > m vanish and those with a + b = m equal 1, so the matrix is anti-triangular with unit anti-diagonal and D_m is odd. If m is even, write m = 2^v s with s odd and v >= 1 and take j = 2^v - 1: over the field with two elements (1 + X)^m = (1 + X^(2^v))^s, so for a + b < 2^(v+1) the coefficient C(m, a + b) is odd exactly when a + b is 0 or 2^v, the matrix is the permutation matrix of 0 -> 0, a -> 2^v - a, and D_j is odd. In both cases j is odd, and comparing 2-adic valuations in D_j = 2^j Q^2 gives 0 = j + 2 v_2(Q), which is impossible. The source proves the conjecture for n = 4 and, for odd n, for n congruent to 3 or 5 modulo 8, from the irrationality of the weight next to the middle vertex; these are the sizes for which the determinant D_1 is odd. This is partial progress on the conjecture of the source: m = 1 gives n = 3, below the range n >= 4 of the conjecture; every odd n >= 5 is covered, the sizes beyond the cases of the source being those congruent to 1 or 7 modulo 8; the even sizes n >= 6 are not addressed.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.middle_moment_gram_det`
- Truth anchor: `D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.result`
- Dependency: [D5/S3/Quantum/Dynamics/PathMiddleVertexMoments](PathMiddleVertexMoments.md)
