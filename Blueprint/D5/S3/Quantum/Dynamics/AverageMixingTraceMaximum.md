# The complete graph maximizes the trace of the average mixing matrix

## Abstract

For every n and every connected graph G on n vertices, the trace of the average mixing matrix of the adjacency quantum walk on G is at most that of the complete graph K_n. This proves Conjecture 9.1 of C. Godsil, K. Guo and M. Sobchuk (arXiv:1910.02039), read over connected graphs.

**Definition 1.1 (The spectral idempotents).**

$$\operatorname{idempotent}\left(G, \theta\right) = \sum_{i: \lambda_{i} = \theta} v_{i} \left(v_{i}\right)^{T}$$

*Formalization.* `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.idempotent` (`✓ std3`).

*Citation.* Chris Godsil; Krystal Guo; Mariia Sobchuk (2023). *Diagonal entries of the average mixing matrix*. DOI: [10.48550/arXiv.1910.02039](https://doi.org/10.48550/arXiv.1910.02039). URL: <https://arxiv.org/abs/1910.02039v1>.

*Commentary.*

For a simple graph G on the vertex set Fin n, with decidable adjacency, the adjacency matrix A(G) is a real symmetric matrix. Let v_1, ..., v_n be the orthonormal eigenbasis of A(G) chosen by Mathlib (Matrix.IsHermitian.eigenvectorBasis), with eigenvalues lambda_1, ..., lambda_n (Matrix.IsHermitian.eigenvalues). E_theta(G) is the sum of the outer products v_i v_i^T over the indices i with lambda_i = theta. It is the orthogonal projection onto the theta-eigenspace of A(G), whatever orthonormal eigenbasis is chosen, and it is the zero matrix when theta is not an eigenvalue.

**Definition 1.2 (The average mixing matrix).**

$$\operatorname{avgMixing}\left(G\right) = \sum_{\theta \in \{\lambda_{i} : i \in \operatorname{Fin}\left(n\right)\}} \operatorname{idempotent}\left(G, \theta\right) \circ \operatorname{idempotent}\left(G, \theta\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.avgMixing` (`✓ std3`).

*Citation.* Chris Godsil; Krystal Guo; Mariia Sobchuk (2023). *Diagonal entries of the average mixing matrix*. DOI: [10.48550/arXiv.1910.02039](https://doi.org/10.48550/arXiv.1910.02039). URL: <https://arxiv.org/abs/1910.02039v1>.

*Commentary.*

The paper writes A = sum_r theta_r E_r over the distinct eigenvalues theta_r and quotes Godsil (2013): the average mixing matrix is the sum over r of the Schur products E_r o E_r. Here the sum runs over the set of eigenvalues {lambda_i : i in Fin n}, each distinct eigenvalue once, and o is the Schur (entrywise) product of matrices.

**Definition 1.3 (Conjecture 9.1).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N}, \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{Connected}\left(G\right) \Rightarrow \operatorname{trace}\left(\operatorname{avgMixing}\left(G\right)\right) \le \operatorname{trace}\left(\operatorname{avgMixing}\left(K_{n}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.claim` (`✓ std3`).

*Citation.* Chris Godsil; Krystal Guo; Mariia Sobchuk (2023). *Diagonal entries of the average mixing matrix*. DOI: [10.48550/arXiv.1910.02039](https://doi.org/10.48550/arXiv.1910.02039). URL: <https://arxiv.org/abs/1910.02039v1>.

*Commentary.*

C. Godsil, K. Guo and M. Sobchuk, arXiv:1910.02039, Section 9 (Open problems), state after Table 2 and Corollary 6.3, as Conjecture 9.1 of the published version (Australas. J. Combin. 86(3) (2023)): "The complete graph on $n$ vertices attains the maximum trace with respect to the $\widehat{M}_{A}$ for all $n$." The maximum is read over connected graphs on n vertices, as in the 2026 restatement of A. Mohan, C. Tamon, Y. Xu and H. Zhan (arXiv:2608.20739); over all graphs the empty graph would have trace n. In the formula G ranges over the simple graphs on Fin n with decidable adjacency, Connected is SimpleGraph.Connected, and K_n is the complete graph, the top element of SimpleGraph (Fin n). Connected graphs are nonempty, so n is at least 1.

**Theorem 1.4 (The complete graph attains the maximum).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/godsil-2023-average-mixing-trace-maximum` (proved) by `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"godsil-2023-average-mixing-trace-maximum","declaration_gid":"D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chris Godsil; Krystal Guo; Mariia Sobchuk (2023). *Diagonal entries of the average mixing matrix*. DOI: [10.48550/arXiv.1910.02039](https://doi.org/10.48550/arXiv.1910.02039). URL: <https://arxiv.org/abs/1910.02039v1>.

*Commentary.*

Fix a vertex a with a neighbour and an eigenvalue theta, and let q be the diagonal entry of E_theta at a. The column u = E_theta e_a satisfies A u = theta u, u_a = q and |u|^2 = q, so the coordinates of u off a have squared norm q - q^2. Cauchy-Schwarz on the eigen-equation at a gives theta^2 q^2 <= (n - 1)(q - q^2). At a neighbour b of a, q = theta u_b minus the sum of u_c over the other neighbours c of b, a combination over deg(b) vertices other than a, so q^2 <= (theta^2 + n - 2)(q - q^2). Eliminating theta gives (q^2 - (n - 1)(q - q^2))(q^2 + q - q^2) <= 0, hence q^2 <= (n - 1) q (1 - q) and n q <= n - 1. The diagonal entries of the E_theta at a are nonnegative and sum to 1, and each is at most 1 - 1/n, so the sum of their squares, which is the diagonal entry of the average mixing matrix at a, is at most 1 - 2/n + 2/n^2. In a connected graph with n >= 2 every vertex has a neighbour, so the trace is at most n - 2 + 2/n; for n = 1 the trace is 1. For K_n with n >= 2, an eigenvector with eigenvalue other than -1 is constant with eigenvalue n - 1, and the trace of A(K_n) is 0, so exactly one eigenbasis vector has eigenvalue n - 1; hence the diagonal entries of E_(n-1) and E_(-1) are 1/n and 1 - 1/n, and the trace of the average mixing matrix of K_n is n - 2 + 2/n, as computed in the paper.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.avgMixing`
- Truth anchor: `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.idempotent`
- Truth anchor: `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.result`
