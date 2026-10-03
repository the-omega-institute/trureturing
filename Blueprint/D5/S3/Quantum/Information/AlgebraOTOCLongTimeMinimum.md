# The minimum of the long-time algebra OTOC

## Abstract

For a block structure with sectors of type (n_J, d_J), J = 1, ..., r, and D = sum_J n_J d_J, the non-resonant long-time average of the algebra OTOC over all eigenbases of the D-dimensional Hilbert space is at least 1 - (sum_J d_J + sum_J n_J - r) / D, and the product basis attains this value. This proves the conjecture of F. Andreadakis, E. Dallas and P. Zanardi (arXiv:2312.13386, Section IV).

**Definition 1.1 (The projection onto the algebra).**

$$\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall X : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \operatorname{projA}\left(n, d, X\right) = \operatorname{blockDiagonal}\left((J \mapsto \frac{1}{n_{J}} \cdot \operatorname{kronecker}\left(\operatorname{I}\left(n_{J}\right), \operatorname{partialTraceLeft}\left(\operatorname{blockDiag}\left(X, J\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.projA` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

The Hilbert space is the direct sum over J of C^{n_J} tensor C^{d_J}, indexed by Idx(n, d), the pairs (J, (a, b)) with a < n_J and b < d_J. The algebra A acts as the identity on each C^{n_J} and arbitrarily on each C^{d_J}. Its Hilbert-Schmidt projection keeps the diagonal block X_J of X, traces out the first factor and spreads the result evenly over it: P_A(X) is the block-diagonal matrix with blocks (1/n_J) I_{n_J} tensor Tr_{n_J}(X_J).

**Definition 1.2 (The projection onto the commutant).**

$$\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall X : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \operatorname{projAc}\left(n, d, X\right) = \operatorname{blockDiagonal}\left((J \mapsto \frac{1}{d_{J}} \cdot \operatorname{kronecker}\left(\operatorname{partialTraceRight}\left(\operatorname{blockDiag}\left(X, J\right)\right), \operatorname{I}\left(d_{J}\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.projAc` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

The commutant A' acts arbitrarily on each C^{n_J} and as the identity on each C^{d_J}. Its Hilbert-Schmidt projection is the block-diagonal matrix with blocks Tr_{d_J}(X_J) tensor (1/d_J) I_{d_J}.

**Definition 1.3 (Rank-one operators of an eigenbasis).**

$$\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall U : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \forall k : \operatorname{Idx}\left(n, d\right), \forall l : \operatorname{Idx}\left(n, d\right), \forall i : \operatorname{Idx}\left(n, d\right), \forall j : \operatorname{Idx}\left(n, d\right), \operatorname{entry}\left(\operatorname{ketBra}\left(U, k, l\right), i, j\right) = \operatorname{U}\left(i, k\right) \cdot \overline{\operatorname{U}\left(j, l\right)}$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.ketBra` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

For a matrix U whose columns phi_k form the eigenbasis, ketBra(U, k, l) is the operator |phi_k><phi_l|, with entries U(i, k) times the complex conjugate of U(j, l).

**Definition 1.4 (The first kernel).**

$$\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall P : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)} \to \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \forall U : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \forall l : \operatorname{Idx}\left(n, d\right), \forall k : \operatorname{Idx}\left(n, d\right), \operatorname{entry}\left(\operatorname{R0}\left(P, U\right), l, k\right) = \operatorname{Re}\left(\operatorname{Tr}\left(\operatorname{P}\left(\operatorname{ketBra}\left(U, k, l\right)\right)^{*} \operatorname{P}\left(\operatorname{ketBra}\left(U, k, l\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.R0` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

R^(0)(P, U) has (l, k) entry the squared Hilbert-Schmidt norm of P(|phi_k><phi_l|).

**Definition 1.5 (The second kernel).**

$$\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall P : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)} \to \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \forall U : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \forall k : \operatorname{Idx}\left(n, d\right), \forall l : \operatorname{Idx}\left(n, d\right), \operatorname{entry}\left(\operatorname{R1}\left(P, U\right), k, l\right) = \operatorname{Re}\left(\operatorname{Tr}\left(\operatorname{P}\left(\operatorname{ketBra}\left(U, k, k\right)\right)^{*} \operatorname{P}\left(\operatorname{ketBra}\left(U, l, l\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.R1` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

R^(1)(P, U) has (k, l) entry the Hilbert-Schmidt inner product of P(Pi_k) and P(Pi_l), with Pi_k = |phi_k><phi_k|. For the two projections above both images are Hermitian, so the inner product is real and equals the real part of the trace.

**Definition 1.6 (One summand of the long-time average).**

$$\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall R : \mathbb{R}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \forall S : \mathbb{R}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \operatorname{term}\left(R, S\right) = \operatorname{Tr}\left(R S\right) - \frac{1}{2} \cdot \operatorname{Tr}\left(\operatorname{diagonal}\left(\operatorname{diag}\left(R\right)\right) \operatorname{diagonal}\left(\operatorname{diag}\left(S\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.term` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

For real square matrices R and S, term(R, S) is Tr(R S) minus one half of the trace of the product of the diagonal matrices carrying the diagonals of R and S.

**Definition 1.7 (The non-resonant long-time average).**

$$\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall U : \mathbb{C}^{\operatorname{Idx}\left(n, d\right) \times \operatorname{Idx}\left(n, d\right)}, \operatorname{lta}\left(n, d, U\right) = 1 - \frac{1}{\sum_{J} n_{J} \cdot d_{J}} \cdot (\operatorname{term}\left(\operatorname{R0}\left(\operatorname{projA}\left(n, d\right), U\right), \operatorname{R1}\left(\operatorname{projAc}\left(n, d\right), U\right)\right) + \operatorname{term}\left(\operatorname{R0}\left(\operatorname{projAc}\left(n, d\right), U\right), \operatorname{R1}\left(\operatorname{projA}\left(n, d\right), U\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.lta` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

The long-time average of the A-OTOC under the non-resonance condition, the paper's Eq. (6), for the Hamiltonian whose eigenbasis is given by the columns of U. The sum runs over the two orders (A, A') and (A', A) of the algebra and its commutant, and D = sum_J n_J d_J is the dimension.

**Definition 1.8 (The conjecture).**

$$claim \Leftrightarrow (\forall r : \mathbb{N}, \forall n : \operatorname{Fin}\left(r\right) \to \mathbb{N}, \forall d : \operatorname{Fin}\left(r\right) \to \mathbb{N}, (\forall J : \operatorname{Fin}\left(r\right), 0 < n_{J}) \Rightarrow ((\forall J : \operatorname{Fin}\left(r\right), 0 < d_{J}) \Rightarrow (\operatorname{IsLeast}\left(\ \{\operatorname{lta}\left(n, d, U\right) \mid U \in \operatorname{unitaryGroup}\left(\operatorname{Idx}\left(n, d\right), \mathbb{C}\right)\ \}, 1 - \frac{\sum_{J} d_{J} + \sum_{J} n_{J} - r}{\sum_{J} n_{J} \cdot d_{J}}\right))))$$

*Formalization.* `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.claim` (`✓ std3`).

*Citation.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

The paper fixes the algebra class and asks for the algebra of that class that minimizes the long-time average for a given Hamiltonian; by the algebra-Hamiltonian duality used in its Section IV A this is the same as fixing the algebra in its distinguished basis and varying the eigenbasis U over the unitary group. The conjecture states that the least value is 1 - (sum_J d_J + sum_J n_J - r) / D, attained by the eigenbasis of product vectors in the distinguished basis. Here r is the number of sectors, d_Z in the paper.

**Theorem 1.9 (The conjecture holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/andreadakis-2024-algebra-otoc-long-time-minimum` (proved) by `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andreadakis-2024-algebra-otoc-long-time-minimum","declaration_gid":"D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi (2024). *Long-time Quantum Scrambling and Generalized Tensor Product Structures*. DOI: [10.1103/PhysRevA.109.052424](https://doi.org/10.1103/PhysRevA.109.052424). URL: <https://arxiv.org/abs/2312.13386v2>.

*Commentary.*

Write the J block of phi_k as an n_J x d_J matrix C, its weight q = |C|^2 (squared Frobenius norm) and its purity p = Tr((C C^*)^2). Let F be D times one minus the long-time average. The (k, l) entry of R^(1) for the commutant projection is a sum over J of Tr(Tr_{d_J}(Pi_k) Tr_{d_J}(Pi_l)) / d_J. For any coefficients c_k this quadratic form equals the sum over J of the squared Frobenius norm of Tr_{d_J}(Y_J) divided by d_J, where Y = U diag(c) U^*; by Cauchy-Schwarz in each block this is at most the squared Frobenius norm of Y, which is the sum of |c_k|^2 because U is unitary. So that kernel lies below the identity, and the same holds for the other projection. The matching R^(0) is a sum of Gram matrices, so each cross trace Tr(R^(0) R^(1)) is at most the trace of R^(0), and the diagonal entries of R^(0) are sums of purities divided by n_J or d_J, at most the corresponding sums of q^2. With x + y - x y increasing on the unit square and q summing to 1 over J for each k and to n_J d_J over k for each J, F is at most the sum over J of ((n_J + d_J) sum_k q^2 - sum_k q^4) / (n_J d_J). For n_J + d_J = M at least 3, (M - 1) x - M x^2 + x^4 = x (1 - x) (M - 1 - x - x^2) is nonnegative on [0, 1], so the J term is at most n_J + d_J - 1; for n_J = d_J = 1, 2 x^2 - x^4 is superadditive on the simplex, so the term is at most 1. Hence F is at most sum_J (n_J + d_J - 1), which is the lower bound. At U = 1 the entries of the four kernels are indicator functions of equal first or second coordinates within a block, scaled by 1/n_J or 1/d_J, and the two cross traces equal sum_J d_J and sum_J n_J while both diagonal traces equal r; so the identity attains the bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.R0`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.R1`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.claim`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.ketBra`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.lta`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.projA`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.projAc`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.result`
- Truth anchor: `D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.term`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
