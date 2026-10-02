# The signed Pauli sum bound fails for three qubits

## Abstract

For three qubits, one choice of signs makes the signed sum of all 63 non-identity Pauli words an operator with eigenvalue 21, hence of norm at least 21, above (sqrt(3) + 1)^3 - 1 = 9 + 6 sqrt(3). This refutes the conjecture of O. Liabotro (arXiv:1607.02667, Eq. (78)) that every such signed sum on m qubits has norm at most (sqrt(3) + 1)^m - 1.

**Definition 1.1 (Pauli labels of base-4 digits).**

$$\operatorname{sigmaOfDigit}\left(0\right) = I, \operatorname{sigmaOfDigit}\left(1\right) = X, \operatorname{sigmaOfDigit}\left(2\right) = Y, \operatorname{sigmaOfDigit}\left(c\right) = Z, c \ge 3$$

*Formalization.* `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.sigmaOfDigit` (`✓ std3`).

*Citation.* Ola Liabøtrø (2017). *Improved Classical and Quantum Random Access Codes*. DOI: [10.1103/PhysRevA.95.052315](https://doi.org/10.1103/PhysRevA.95.052315). URL: <https://arxiv.org/abs/1607.02667v2>.

*Commentary.*

The Pauli label of a base-4 digit c: sigma~_0 = I, sigma~_1 = X, sigma~_2 = Y and sigma~_3 = Z.

**Definition 1.2 (Signed sums of Pauli words).**

$$\operatorname{signedPauliSum}\left(\beta\right) = \sum_{k = 1}^{4^{m} - 1} (-1)^{\beta\left(k\right)} \cdot \operatorname{wordOp}\left(i \mapsto \operatorname{sigmaOfDigit}\left(\lfloor\frac{k}{4^{i}}\rfloor \mathrm{mod} 4\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.signedPauliSum` (`✓ std3`).

*Citation.* Ola Liabøtrø (2017). *Improved Classical and Quantum Random Access Codes*. DOI: [10.1103/PhysRevA.95.052315](https://doi.org/10.1103/PhysRevA.95.052315). URL: <https://arxiv.org/abs/1607.02667v2>.

*Commentary.*

For a sign function beta on the indices k, the sum over k = 1, ..., 4^m - 1 of (-1)^beta(k) times the word operator wordOp(g_k) = P_(g_k(0)) tensor ... tensor P_(g_k(m-1)), where g_k(i) = sigmaOfDigit(floor(k / 4^i) mod 4) is the Pauli label of the base-4 digit of k at qubit i and P_I = I, P_X = X, P_Y = iXZ, P_Z = Z are the Pauli matrices. This is the matrix Sigma(beta) of the paper, with c_(i+1)(k) the digit at qubit i.

**Definition 1.3 (The conjectured norm bound).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; \forall \beta : \mathbb{N} \to \operatorname{Fin}\left(2\right), \left\lVert \operatorname{signedPauliSum}\left(\beta\right) \right\rVert \le (\sqrt{3} + 1)^{m} - 1)$$

*Formalization.* `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.claim` (`✓ std3`).

*Citation.* Ola Liabøtrø (2017). *Improved Classical and Quantum Random Access Codes*. DOI: [10.1103/PhysRevA.95.052315](https://doi.org/10.1103/PhysRevA.95.052315). URL: <https://arxiv.org/abs/1607.02667v2>.

*Commentary.*

The conjecture of the paper: for every number m of qubits and every sign function beta on the natural numbers (only its values at k = 1, ..., 4^m - 1 enter), the operator norm of Sigma(beta) is at most (sqrt(3) + 1)^m - 1. The norm is the operator norm for the Euclidean norm on C^(2^m). The paper checks m = 1 and m = 2 exhaustively.

**Theorem 1.4 (The conjectured bound fails for three qubits).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liabotro-2017-signed-pauli-sum-norm` (refuted) by `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liabotro-2017-signed-pauli-sum-norm","declaration_gid":"D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ola Liabøtrø (2017). *Improved Classical and Quantum Random Access Codes*. DOI: [10.1103/PhysRevA.95.052315](https://doi.org/10.1103/PhysRevA.95.052315). URL: <https://arxiv.org/abs/1607.02667v2>.

*Commentary.*

Take m = 3 and v = (-1 + 2i, 1, 1, 1, 1, 1, 1, 1), the first coordinate being the all-zero basis label. For every non-identity word P the number <v, P v> is 4 or -4; choose beta(k) = 0 when it is 4 for the word P whose letters are the base-4 digits of k, and beta(k) = 1 otherwise; the digits of k = 1, ..., 63 run once over the 63 non-identity words. A kernel-checked computation over the Gaussian integers gives Sigma(beta) v = 21 v, and the ring map from the Gaussian integers to C carries it to the complex matrices. Since v is nonzero and the operator norm bounds |Sigma(beta) v| by the norm times |v|, the norm of Sigma(beta) is at least 21. On the other side (sqrt(3) + 1)^3 - 1 = 9 + 6 sqrt(3) < 21 because sqrt(3) < 2, so the conjectured bound fails for m = 3.

## References

- Truth anchor: `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.sigmaOfDigit`
- Truth anchor: `D5/S3/Quantum/Information/SignedPauliSumNormRefutation.signedPauliSum`
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](StabilizerPairLocalUnitaryInequivalence.md)
- Dependency: [D5/S3/Quantum/Measurement/HoggarSicSumNegativity](../Measurement/HoggarSicSumNegativity.md)
