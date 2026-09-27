# Positive Singular-Support Columns and Diagonalization

## Abstract

Positive singular-support candidate columns admit an explicit real diagonalization.

**Definition 1.1 (The singular-support radius).**

$$z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R} \Rightarrow \operatorname{r}(z, p) = \sqrt{{z}^{2}+{p_{0}}^{2}+{p_{1}}^{2}}.$$

*Formalization.* `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.r` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius combines the distinguished positive coordinate with the two support coordinates.

**Definition 1.2 (The unnormalized support block).**

$$z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R} \Rightarrow \operatorname{gZero}(z, p) = z \operatorname{r}(z, p) I_{2} + \frac{\operatorname{r}(z, p)}{\operatorname{r}(z, p)+z} \operatorname{vecMulVec}(p, p).$$

*Formalization.* `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.gZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support block is a positive scalar identity plus a positive rank-one matrix.

**Definition 1.3 (The column-normalization matrix).**

$$z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R}, \operatorname{H}(z, p) = \operatorname{diagonal}((j \mapsto \frac{p_{j}}{\operatorname{r}(z, p) \sqrt{{z}^{2}+{p_{j}}^{2}}})).$$

*Formalization.* `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each diagonal entry normalizes one support column by its radius and planar length.

**Definition 1.4 (The normalized support block).**

$$z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R} \Rightarrow \operatorname{K}(z, p) = \operatorname{gZero}(z, p) \operatorname{H}(z, p).$$

*Formalization.* `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Right multiplication by the diagonal normalization rescales the two columns of the support block.

**Definition 1.5 (The distinguished eigenvalue).**

$$z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R} \Rightarrow \operatorname{q}(z, p) = \frac{1}{\operatorname{r}(z, p)} \sum_{j \in \operatorname{Fin}(2)} p_{j} \sqrt{{z}^{2}+{p_{j}}^{2}}.$$

*Formalization.* `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinguished eigenvalue is the radius-normalized sum of the two weighted planar lengths.

**Definition 1.6 (The final candidate column).**

$$z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R} \Rightarrow \operatorname{u}(z, p) = \frac{1}{z} (\operatorname{q}(z, p) I_{2} - \operatorname{K}(z, p)) p.$$

*Formalization.* `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The final column is the scaled residual of the distinguished eigenvalue equation on the positive support vector.

**Definition 1.7 (The three-dimensional block candidate).**

$$z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R} \Rightarrow \operatorname{Q}(z, p) = \operatorname{fromBlocks}(\operatorname{K}(z, p), \operatorname{u}(z, p), 0, \operatorname{q}(z, p)).$$

*Formalization.* `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The candidate is block upper triangular with support block K, final column u, and scalar block q.

**Theorem 1.8 (Positive columns and explicit real diagonalization).**

$$\begin{gathered}\forall z: \mathbb{R}, p: (\operatorname{Fin}(2)) \to \mathbb{R},\\ 0 < z \land (\forall j: \operatorname{Fin}(2), 0 < p_{j}) \Rightarrow \\ (\forall j: \operatorname{Fin}(2), 0 < \operatorname{u}(z, p)_{j}) \land \\ (\forall i: \operatorname{Fin}(2), j: \operatorname{Fin}(2), 0 < \operatorname{K}(z, p)_{ij}) \land \\ \exists \lambda_{1}: \mathbb{R}, \lambda_{2}: \mathbb{R}, 0 < \lambda_{1} \land \lambda_{1} < \operatorname{q}(z, p) \land 0 < \lambda_{2} \land \lambda_{2} < \operatorname{q}(z, p) \land \\ \exists S: \operatorname{Matrix}(\operatorname{Sum}(\operatorname{Fin}(2), \operatorname{Fin}(1)), \operatorname{Sum}(\operatorname{Fin}(2), \operatorname{Fin}(1)), \mathbb{R}), \operatorname{IsUnit}(\operatorname{det}(S)) \land \\ \operatorname{Q}(z, p) S = S \operatorname{fromBlocks}(\operatorname{diagonal}(![\lambda_{1}, \lambda_{2}]), 0, 0, \operatorname{const}(\operatorname{q}(z, p))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.singular_support_candidate_positive_and_diagonalizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each component, eliminating the radial factor gives the displayed two-coordinate positivity identity. The ratio of the two diagonal normalizations is strictly below the corresponding square-root bound, which makes both residual components positive.

The unnormalized support block is positive definite. Conjugating it by the positive square root of the normalization gives a real symmetric positive-definite matrix. Its spectral decomposition supplies two positive eigenvalues and an invertible eigenbasis for K.

The identity Kp+zu=qp makes every weighted row sum strictly smaller than q. Applying the maximum-ratio argument to an eigenvector places both support eigenvalues below q.

Adjoining p/z to the support eigenbasis gives the explicit upper-triangular block change of basis. The relation Kp+zu=qp proves the final column equation, and invertibility follows because the change of basis is block upper-triangular with invertible diagonal blocks.

## References

- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.H`
- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.K`
- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.Q`
- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.gZero`
- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.q`
- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.r`
- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.singular_support_candidate_positive_and_diagonalizable`
- Truth anchor: `D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.u`
