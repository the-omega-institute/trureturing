# A nice error basis code whose stabilizer group is not normal

## Abstract

In the projective error model of Proposition 8.1 with n = 2, a group of order 16 acting on C^4, the code spanned by (1, 1, 1, 1) has four logical operators and four stabilizers, so their orders multiply to the order of the group, yet the stabilizers do not form a normal subgroup.

**Definition 1.1 (Projective representations).**

$$\operatorname{IsProjRep}\left(pi\right) \Leftrightarrow ((\forall x \in G,\; \operatorname{pi}\left(x\right) \in \operatorname{unitaryGroup}\left(d\right)) \land (\forall x \in G,\; \forall y \in G,\; \exists c \in \mathbb{C},\; (\left\lVert c \right\rVert = 1) \land (\operatorname{pi}\left(x\right) \cdot \operatorname{pi}\left(y\right) = c \cdot \operatorname{pi}\left(x \cdot y\right))))$$

*Formalization.* `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.IsProjRep` (`✓ std3`).

*Citation.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

Every pi(x) is a unitary matrix, and pi(x) pi(y) is a unit complex multiple of pi(xy), so that composing with the quotient by scalars gives a group homomorphism.

**Definition 1.2 (Projective faithfulness).**

$$\operatorname{ProjFaithful}\left(pi\right) \Leftrightarrow (\forall x \in G,\; \forall y \in G,\; (\exists c \in \mathbb{C},\; \operatorname{pi}\left(x\right) = c \cdot \operatorname{pi}\left(y\right)) \Rightarrow (x = y))$$

*Formalization.* `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.ProjFaithful` (`✓ std3`).

*Citation.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

The composite of pi with the quotient by scalars is injective.

**Definition 1.3 (Irreducibility).**

$$\operatorname{IrredProj}\left(pi\right) \Leftrightarrow (\forall U \in \operatorname{Submodule}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, d\right)\right),\; (\forall x \in G,\; \forall v \in U,\; \operatorname{apply}\left(\operatorname{pi}\left(x\right), v\right) \in U) \Rightarrow ((U = 0) \lor (U = V)))$$

*Formalization.* `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.IrredProj` (`✓ std3`).

*Citation.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

The only subspaces of the Euclidean space C^d invariant under every pi(x) are 0 and the whole space.

**Definition 1.4 (Projective error models).**

$$\operatorname{IsPEM}\left(pi\right) \Leftrightarrow (((\operatorname{IsProjRep}\left(pi\right)) \land (\operatorname{ProjFaithful}\left(pi\right))) \land (\operatorname{IrredProj}\left(pi\right)))$$

*Formalization.* `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.IsPEM` (`✓ std3`).

*Citation.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

A projective error model is a projectively faithful irreducible projective representation of a finite group.

**Definition 1.5 (Logical operators).**

$$\forall x \in G,\; x \in \operatorname{logicalOps}\left(pi, W\right) \Leftrightarrow (\forall v \in \operatorname{EuclideanSpace}\left(\mathbb{C}, d\right),\; \operatorname{P}\left(W, \operatorname{apply}\left(\operatorname{pi}\left(x\right), v\right)\right) = \operatorname{apply}\left(\operatorname{pi}\left(x\right), \operatorname{P}\left(W, v\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.logicalOps` (`✓ std3`).

*Citation.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

The elements whose matrices commute with the orthogonal projection P_W onto the code W.

**Definition 1.6 (Stabilizers).**

$$\forall x \in G,\; x \in \operatorname{stabilizers}\left(pi, W\right) \Leftrightarrow (\exists c \in \mathbb{C},\; (\left\lVert c \right\rVert = 1) \land (\forall v \in \operatorname{EuclideanSpace}\left(\mathbb{C}, d\right),\; \operatorname{P}\left(W, \operatorname{apply}\left(\operatorname{pi}\left(x\right), \operatorname{P}\left(W, v\right)\right)\right) = c \cdot \operatorname{P}\left(W, v\right)))$$

*Formalization.* `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.stabilizers` (`✓ std3`).

*Citation.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

The elements for which P_W pi(x) P_W is a unit complex multiple of P_W.

**Definition 1.7 (The negative answer to Question 11.3).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; \forall G \in \operatorname{FiniteGroup},\; \forall pi \in G \to \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \forall W \in \operatorname{Submodule}\left(\operatorname{EuclideanSpace}\left(\mathbb{C}, d\right)\right),\; (((\operatorname{IsPEM}\left(pi\right)) \land (\operatorname{card}\left(G\right) = d^{2})) \land (\operatorname{ncard}\left(\operatorname{logicalOps}\left(pi, W\right)\right) \cdot \operatorname{ncard}\left(\operatorname{stabilizers}\left(pi, W\right)\right) = \operatorname{card}\left(G\right))) \Rightarrow (\forall g \in G,\; \forall s \in \operatorname{stabilizers}\left(pi, W\right),\; g \cdot s \cdot \operatorname{inv}\left(g\right) \in \operatorname{stabilizers}\left(pi, W\right)))$$

*Formalization.* `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.claim` (`✓ std3`).

*Citation.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

For every projective error model on C^d with a group of order d^2 and every subspace W, if the orders of the logical operators and of the stabilizers multiply to the order of the group, then the stabilizers are closed under conjugation. Question 11.3 asks whether this can fail.

**Theorem 1.8 (The example).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.result` (`✓ std3`). ∎

*Resolves.* `Problems/eidesen-2025-nice-error-basis-non-normal-stabilizer` (refuted) by `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"eidesen-2025-nice-error-basis-non-normal-stabilizer","declaration_gid":"D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jonas Eidesen (2025). *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*. DOI: [10.48550/arXiv.2506.01843](https://doi.org/10.48550/arXiv.2506.01843). URL: <https://arxiv.org/abs/2506.01843v3>.

*Commentary.*

Take the model of Proposition 8.1 with n = 2: the group C2 x D_4 generated by c, b and a of order 4 acts on C^4 by the block swap C, the block-diagonal matrix diag(X, X) with X the Pauli matrix, and the block-diagonal matrix diag(P, -P) with P = diag(1, i). All sixteen matrices are monomial with entries 0, +-1, +-i. Over the Gaussian integers one checks that they are unitary, that each product pi(x) pi(y) equals pi(xy) times one of 1, -1, i, -i, that distinct elements have trace-orthogonal matrices, and that each matrix unit E_kl equals one quarter of the sum of conj(pi(x)_kl) pi(x). The last identity makes every invariant subspace invariant under all matrices, hence 0 or C^4; trace orthogonality makes pi projectively faithful. For W spanned by u = (1, 1, 1, 1), the orthogonal projection is v -> (sum of v_i / 4) u, so x is a logical operator exactly when every column sum of pi(x) equals every row sum, and a stabilizer exactly when the sum of all entries has absolute value 4. Both hold exactly for the four elements 1, b, c, bc, so 4 x 4 = 16 is the order of the group, while a b a^-1 = b a^2 is not among them.

## References

- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.IrredProj`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.IsPEM`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.IsProjRep`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.ProjFaithful`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.claim`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.logicalOps`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.result`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.stabilizers`
