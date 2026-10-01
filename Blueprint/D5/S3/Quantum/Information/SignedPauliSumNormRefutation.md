# The signed Pauli sum bound fails for three qubits

## Abstract

For three qubits, one choice of signs makes the signed sum of all 63 non-identity Pauli words an operator with eigenvalue 21, hence of norm at least 21, above (sqrt(3) + 1)^3 - 1 = 9 + 6 sqrt(3). This refutes the conjecture of O. Liabotro (arXiv:1607.02667, Eq. (78)) that every such signed sum on m qubits has norm at most (sqrt(3) + 1)^m - 1.

**Definition 1.1 (Signed sums of Pauli words).**

$$\operatorname{signedPauliSum}\left(\beta\right) = \sum_{g : \operatorname{Fin}\left(m\right) \to Pauli, g \ne \mathbf{I}} (-1)^{\beta\left(g\right)} \cdot \operatorname{wordOp}\left(g\right)$$

*Formalization.* `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.signedPauliSum` (`✓ std3`).

*Citation.* Ola Liabøtrø (2017). *Improved Classical and Quantum Random Access Codes*. DOI: [10.1103/PhysRevA.95.052315](https://doi.org/10.1103/PhysRevA.95.052315). URL: <https://arxiv.org/abs/1607.02667v2>.

*Commentary.*

For a sign function beta on the Pauli words g of m qubits, the sum over all words other than the identity word I (the word whose every letter is I) of (-1)^beta(g) times the word operator wordOp(g) = P_(g_1) tensor ... tensor P_(g_m), where P_I = I, P_X = X, P_Y = iXZ and P_Z = Z are the Pauli matrices. This is the matrix Sigma(beta) of the paper, whose index k runs over the base-4 digit strings of 1, ..., 4^m - 1, that is, over the non-identity words.

**Definition 1.2 (The conjectured norm bound).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; \forall \beta : (\operatorname{Fin}\left(m\right) \to Pauli) \to \operatorname{Fin}\left(2\right), \left\lVert \operatorname{signedPauliSum}\left(\beta\right) \right\rVert \le (\sqrt{3} + 1)^{m} - 1)$$

*Formalization.* `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.claim` (`✓ std3`).

*Citation.* Ola Liabøtrø (2017). *Improved Classical and Quantum Random Access Codes*. DOI: [10.1103/PhysRevA.95.052315](https://doi.org/10.1103/PhysRevA.95.052315). URL: <https://arxiv.org/abs/1607.02667v2>.

*Commentary.*

The conjecture of the paper: for every number m of qubits and every sign function beta, the operator norm of Sigma(beta) is at most (sqrt(3) + 1)^m - 1. The norm is the operator norm for the Euclidean norm on C^(2^m). The paper checks m = 1 and m = 2 exhaustively.

**Theorem 1.3 (The conjectured bound fails for three qubits).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liabotro-2017-signed-pauli-sum-norm` (refuted) by `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liabotro-2017-signed-pauli-sum-norm","declaration_gid":"D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ola Liabøtrø (2017). *Improved Classical and Quantum Random Access Codes*. DOI: [10.1103/PhysRevA.95.052315](https://doi.org/10.1103/PhysRevA.95.052315). URL: <https://arxiv.org/abs/1607.02667v2>.

*Commentary.*

Take m = 3 and v = (-1 + 2i, 1, 1, 1, 1, 1, 1, 1), the first coordinate being the all-zero basis label. For every non-identity word P the number <v, P v> is 4 or -4; choose beta(P) = 0 when it is 4 and beta(P) = 1 otherwise. A kernel-checked computation over the Gaussian integers gives Sigma(beta) v = 21 v, and the ring map from the Gaussian integers to C carries it to the complex matrices. Since v is nonzero and the operator norm bounds |Sigma(beta) v| by the norm times |v|, the norm of Sigma(beta) is at least 21. On the other side (sqrt(3) + 1)^3 - 1 = 9 + 6 sqrt(3) < 21 because sqrt(3) < 2, so the conjectured bound fails for m = 3.

## References

- Truth anchor: `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.signedPauliSum`
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](StabilizerPairLocalUnitaryInequivalence.md)
