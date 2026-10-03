# The upper binegativity bound of Girard and Gour fails

## Abstract

Girard and Gour (arXiv:1701.02724) conjecture that the binegativity of every two-qubit state is at most nu (c + nu)^2 / (2 (c^2 + nu^2)), where nu is the negativity and c the concurrence. The upper bound fails: the rank-two state (|v><v| + 9 |00><00|)/26 with v = (3, 2, 2, 0) has negativity 2/13, concurrence at least 4/13 and binegativity 1/7, while the bound is at most 9/65.

**Definition 1.1 (Binegativity).**

$$\forall sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \operatorname{binegativity}\left(sigma\right) = \operatorname{ReTr}\left(\operatorname{negPart}\left(\operatorname{partialTransposeB}\left(sigma\right)\right)\right) + 2 \cdot \operatorname{ReTr}\left(\operatorname{negPart}\left(\operatorname{partialTransposeB}\left(\operatorname{negPart}\left(\operatorname{partialTransposeB}\left(sigma\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.binegativity` (`✓ std3`).

*Citation.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

For a two-qubit matrix sigma, sigma^Gamma is the partial transposition on the second qubit (the existing partialTransposeB at d = 2) and X_- is the negative part of a self-adjoint matrix X, so that X = X_+ - X_- with X_+ and X_- positive semidefinite and X_+ X_- = 0 (Mathlib's negative part). The binegativity is Tr[(sigma^Gamma)_-] + 2 Tr[(((sigma^Gamma)_-)^Gamma)_-]. The negativity of the paper is N(sigma) = 2 Tr[(sigma^Gamma)_-].

**Definition 1.2 (Concurrence of a pure state).**

$$\forall psi : \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right) \to \mathbb{C}, \operatorname{pureConcurrence}\left(psi\right) = 2 \cdot \left|\operatorname{psi}\left((0, 0)\right) \cdot \operatorname{psi}\left((1, 1)\right) - \operatorname{psi}\left((0, 1)\right) \cdot \operatorname{psi}\left((1, 0)\right)\right|$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.pureConcurrence` (`✓ std3`).

*Citation.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

For a unit vector psi of two qubits, the concurrence is 2 |psi_00 psi_11 - psi_01 psi_10|.

**Definition 1.3 (Concurrence).**

$$\forall sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \operatorname{concurrence}\left(sigma\right) = \operatorname{sInf}\left(\ \{s \mid \exists k : \mathbb{N}, \exists p : \operatorname{Fin}\left(k\right) \to \mathbb{R}, \exists psi : \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right) \to \mathbb{C}, (\forall i : \operatorname{Fin}\left(k\right), 0 \le \operatorname{p}\left(i\right)) \land ((\forall i : \operatorname{Fin}\left(k\right), \sum_{x} \left|\operatorname{\operatorname{psi}\left(i\right)}\left(x\right)\right|^{2} = 1) \land ((sigma = \sum_{i} \operatorname{p}\left(i\right) \cdot \operatorname{vecMulVec}\left(\operatorname{psi}\left(i\right), \operatorname{star}\left(\operatorname{psi}\left(i\right)\right)\right)) \land (s = \sum_{i} \operatorname{p}\left(i\right) \cdot \operatorname{pureConcurrence}\left(\operatorname{psi}\left(i\right)\right))))\ \}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.concurrence` (`✓ std3`).

*Citation.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

The concurrence of a two-qubit state is the infimum of sum_i p_i C(psi_i) over the decompositions sigma = sum_i p_i |psi_i><psi_i| into finitely many unit vectors psi_i with nonnegative weights p_i.

**Definition 1.4 (The conjectured upper bound).**

$$(claim) \Leftrightarrow (\forall sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(sigma\right)) \Rightarrow ((0 < 2 \cdot \operatorname{ReTr}\left(\operatorname{negPart}\left(\operatorname{partialTransposeB}\left(sigma\right)\right)\right)) \Rightarrow (\operatorname{binegativity}\left(sigma\right) \le \frac{2 \cdot \operatorname{ReTr}\left(\operatorname{negPart}\left(\operatorname{partialTransposeB}\left(sigma\right)\right)\right)}{2} \cdot \frac{(\operatorname{concurrence}\left(sigma\right) + 2 \cdot \operatorname{ReTr}\left(\operatorname{negPart}\left(\operatorname{partialTransposeB}\left(sigma\right)\right)\right))^{2}}{\operatorname{concurrence}\left(sigma\right)^{2} + \left(2 \cdot \operatorname{ReTr}\left(\operatorname{negPart}\left(\operatorname{partialTransposeB}\left(sigma\right)\right)\right)\right)^{2}})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.claim` (`✓ std3`).

*Citation.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

The paper conjectures that nu (c + nu)(nu + 1)/((c + nu)^2 + 2c(1 - c)) <= N_2(sigma) <= (nu/2)(c + nu)^2/(c^2 + nu^2) for all states sigma with fixed negativity N(sigma) = nu and concurrence C(sigma) = c. The displayed statement is the upper inequality for every density matrix with positive negativity, which excludes the quotient 0/0 on separable states.

**Definition 1.5 (The counterexample state).**

$$witness = \frac{1}{26} \cdot (\operatorname{vecMulVec}\left(\operatorname{vec4}\left(3, 2, 2, 0\right), \operatorname{star}\left(\operatorname{vec4}\left(3, 2, 2, 0\right)\right)\right) + 9 \cdot \operatorname{vecMulVec}\left(\operatorname{vec4}\left(1, 0, 0, 0\right), \operatorname{star}\left(\operatorname{vec4}\left(1, 0, 0, 0\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.witness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

The state is the mixture of |v><v|/17 with weight 17/26, v = (3, 2, 2, 0) in the basis 00, 01, 10, 11, and of |00><00| with weight 9/26. It is positive semidefinite with trace one.

**Theorem 1.6 (The upper bound fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/girard-2017-binegativity-upper-bound` (refuted) by `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"girard-2017-binegativity-upper-bound","declaration_gid":"D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mark W. Girard; Gilad Gour (2017). *The binegativity of two qubits*. DOI: [10.48550/arXiv.1701.02724](https://doi.org/10.48550/arXiv.1701.02724). URL: <https://arxiv.org/abs/1701.02724v3>.

*Commentary.*

Let A be the partial transpose of the state. With w = (-1, 1, 1, 2), A = (A + ww^T/91) - ww^T/91, where A + ww^T/91 is a sum of three positive rank-one terms with rational coefficients and annihilates w, so the uniqueness of the positive and negative parts gives A_- = ww^T/91, of trace 1/13. In the same way, with z = (2, 3, 3, -2), the negative part of (A_-)^Gamma is 3zz^T/2366, of trace 3/91. Hence the binegativity is 1/13 + 6/91 = 1/7. The negativity 2 Tr[A_-] is therefore 2/13. In every decomposition of the state into pure states, the zero entry at 11,11 forces every vector with positive weight to have zero 11 amplitude, so its concurrence is 2 |psi_01 psi_10| and the triangle inequality gives a total of at least 2 |rho_(01,10)| = 4/13; the rational decomposition with weights 9/13, 1/26, 7/26 and vectors (-7, -4, -4, 0)/9, (1, -2, -2, 0)/3 and (1, 0, 0, 0) shows that the infimum is taken over a nonempty set. For nu = 2/13 the bound (nu/2)(c + nu)^2/(c^2 + nu^2) is at most 9/65 when c >= 4/13, because 9(c^2 + nu^2) - 5(c + nu)^2 = 2(2c - nu)(c - 2nu) >= 0, and 9/65 < 1/7.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.binegativity`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.concurrence`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.pureConcurrence`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation.witness`
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](StructuredNegativityCoincidenceRefutation.md)
