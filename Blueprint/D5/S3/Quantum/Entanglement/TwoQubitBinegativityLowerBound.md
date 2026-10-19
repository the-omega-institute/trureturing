# The two-qubit binegativity lower bound at fixed negativity

## Abstract

For every two-qubit density matrix, the binegativity is bounded below by the Girard–Gour curve at its negativity. The negative eigenvector of the partial transpose has a Schmidt product constrained from below by positivity of the density matrix.

**Definition 1.1 (The lower bound of Girard and Gour).**

$$(claim) \Leftrightarrow (\forall \sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(\sigma\right)) \Rightarrow (\operatorname{let} \nu : \mathbb{R} = 2 \cdot \Re \operatorname{Tr}\left(((\sigma)^{\Gamma})_{-}\right); \operatorname{let} c : \mathbb{R} = \sqrt{2 \cdot \nu \cdot (\nu + 1)} - \nu; \frac{\nu}{2} \cdot (1 + \frac{c}{\sqrt{(1 - c)^{2} + (c)^{2}}}) \le \left(N_{2}\right)\left(\sigma\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.claim` (`✓ std3`).

*Citation.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

Girard and Gour, Eq. (8), conjecture the displayed bound for every two-qubit density matrix sigma. A density matrix is positive semidefinite with trace one. Here nu is its negativity, c = sqrt(2 nu (nu + 1)) - nu, and N_2 is its binegativity. The symbol c denotes this function of nu, rather than the concurrence of an arbitrary state.

For a self-adjoint matrix X, X_- is its positive semidefinite negative component, with X = X_+ - X_- and X_+ X_- = 0. All traces below are taken through their real parts, as in the negativity appearing in the statement. The binegativity is $\forall \sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \left(N_{2}\right)\left(\sigma\right) = \Re \operatorname{Tr}\left(((\sigma)^{\Gamma})_{-}\right) + 2 \cdot \Re \operatorname{Tr}\left(((((\sigma)^{\Gamma})_{-})^{\Gamma})_{-}\right)$.

The partial transpose is on the second qubit: $\forall \sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall i : \operatorname{Fin}\left(2\right), \forall j : \operatorname{Fin}\left(2\right), \forall k : \operatorname{Fin}\left(2\right), \forall l : \operatorname{Fin}\left(2\right), ((\sigma)^{\Gamma})_{(i, j), (k, l)} = (\sigma)_{(i, l), (k, j)}$.

**Theorem 1.2 (The lower bound holds for every two-qubit state).**

$$\forall \sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(\sigma\right)) \Rightarrow (\operatorname{let} \nu : \mathbb{R} = 2 \cdot \Re \operatorname{Tr}\left(((\sigma)^{\Gamma})_{-}\right); \operatorname{let} c : \mathbb{R} = \sqrt{2 \cdot \nu \cdot (\nu + 1)} - \nu; \frac{\nu}{2} \cdot (1 + \frac{c}{\sqrt{(1 - c)^{2} + (c)^{2}}}) \le \left(N_{2}\right)\left(\sigma\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/girard-2017-binegativity-lower-bound` (proved) by `D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"girard-2017-binegativity-lower-bound","declaration_gid":"D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

The partial transpose sigma^Gamma has at most one negative eigenvalue: every two-dimensional subspace of the two-qubit space contains a nonzero product vector, and the quadratic form of sigma^Gamma is nonnegative on product vectors. Thus a two-dimensional negative eigenspace is impossible. If there is a negative eigenvalue -lambda, local unitaries put its unit eigenvector in Schmidt form alpha |00> + beta |11>, with alpha and beta positive and alpha^2 + beta^2 = 1. These unitaries preserve both the negativity N and the binegativity N_2. In these coordinates write a = sigma_(00,00), d = sigma_(11,11), x = a + d, and u = -Re sigma_(01,10). The eigenvalue equations give u^2 = (a + lambda)(d + lambda), nu = 2 lambda, and (2 alpha beta)(x + nu) = 2u. Positivity on |01> + |10> gives 2u <= 1 - x; equivalently, one may use |01> - |10> after a local phase change. Consequently nu (2x + nu) <= (1 - x)^2, so x <= 1 - c. The same eigenvalue equations imply (2 alpha beta)^2 (x + nu)^2 >= nu (2x + nu), which forces 2 alpha beta >= c/sqrt((1 - c)^2 + c^2). Since (sigma^Gamma)_- = lambda |psi><psi|, its partial transpose has the single negative eigenvalue -lambda alpha beta. Therefore N_2(sigma) = (nu/2)(1 + 2 alpha beta), and the lower bound follows. When sigma^Gamma has no negative eigenvalue, its negative component is zero, so nu = c = N_2(sigma) = 0 and both sides vanish.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.result`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio](SeparableNumericalRangeRatio.md)
- Dependency: [D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation](TwoQubitBinegativityUpperBoundRefutation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
