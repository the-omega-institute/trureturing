# Purely non-unital eternal non-Markovianity

## Abstract

A rotating replacement state gives a completely positive trace-preserving qubit dynamics whose unital part is divisible, while its generator fails conditional complete positivity at every positive time.

**Definition 1.1 (The translation-free part).**

$$\forall (Phi: \mathbb{R} \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (t: \mathbb{R}), \forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{unitalPart}\left(Phi, t, X\right) = (Phi\left(t, X\right)) - ((\frac{\operatorname{Matrix.trace}\left(X\right)}{2}) \cdot ((Phi\left(t, 1\right)) - (1)))$$

*Formalization.* `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.unitalPart` (`✓ std3`).

*Citation.* Shrikant Utagi and Subhashish Banerjee and R. Srikanth (2024). *On the eternal non-Markovianity of non-unital quantum channels*. DOI: [10.1142/S0219749923500399](https://doi.org/10.1142/S0219749923500399). URL: <https://arxiv.org/abs/2203.10625>.

*Commentary.*

Eqs. (9)–(11), pages 3–4, decompose the Bloch action into M(t)r + τ(t). On arbitrary complex qubit matrices, subtracting half the trace times Phi(t)(1) − 1 removes the translation. Matrix.trace is the complex trace, 1 is the identity matrix, and the dot is complex scalar multiplication.

**Definition 1.2 (Non-unitality with a divisible unital part).**

$$\forall (Phi: \mathbb{R} \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{PurelyNonUnital}\left(Phi\right) = \left((\forall (t: \mathbb{R}), (0 < t) \Rightarrow (Phi\left(t, 1\right) \ne 1)) \land (\forall (s: \mathbb{R}), \forall (t: \mathbb{R}), (0 \le s) \Rightarrow ((s \le t) \Rightarrow (\exists (V: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{IsCPTP}\left(V\right)) \land (\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), V\left(\operatorname{unitalPart}\left(Phi, s, X\right)\right) = \operatorname{unitalPart}\left(Phi, t, X\right)))))\right)$$

*Formalization.* `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.PurelyNonUnital` (`✓ std3`).

*Citation.* Shrikant Utagi and Subhashish Banerjee and R. Srikanth (2024). *On the eternal non-Markovianity of non-unital quantum channels*. DOI: [10.1142/S0219749923500399](https://doi.org/10.1142/S0219749923500399). URL: <https://arxiv.org/abs/2203.10625>.

*Commentary.*

Definition 1, page 4: "When non-Markovianity originates solely from the non-unital part, i.e., from τ(t), then we call it non-unital non-Markovianity and such a channel will be called purely non-unital non-Markovian channel." Phi(t) fails to preserve 1 for every t > 0. For every 0 ≤ s ≤ t, a completely positive trace-preserving map V carries unitalPart(Phi,s,X) to unitalPart(Phi,t,X) for every matrix X. MatrixMap denotes PhyslibLeaf.MatrixMap, and IsCPTP is the existing completely positive trace-preserving predicate.

**Definition 1.3 (The entrywise time-local generator).**

$$\forall (Phi: \mathbb{R} \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (t: \mathbb{R}), \forall (L: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{IsGeneratorAt}\left(Phi, t, L\right) = \forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (i: \operatorname{Fin}\left(2\right)), \forall (j: \operatorname{Fin}\left(2\right)), \operatorname{HasDerivAt}\left(fun (u: \mathbb{R}) \mapsto Phi\left(u, X, i, j\right), L\left(Phi\left(t, X\right), i, j\right), t\right)$$

*Formalization.* `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.IsGeneratorAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrikant Utagi and Subhashish Banerjee and R. Srikanth (2024). *On the eternal non-Markovianity of non-unital quantum channels*. DOI: [10.1142/S0219749923500399](https://doi.org/10.1142/S0219749923500399). URL: <https://arxiv.org/abs/2203.10625>.

*Commentary.*

The time parameter is real. For each complex matrix X and both Fin 2 indices, HasDerivAt states that the derivative of the entry Phi(u)(X)(i,j) at t equals L(Phi(t)(X))(i,j). No derivative of the input matrix is taken.

**Definition 1.4 (Conditional complete positivity).**

$$\forall (L: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{CondCP}\left(L\right) = \forall (v: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right) \to \mathbb{C}), (\sum_{i: \operatorname{Fin}\left(2\right)} v\left((i, i)\right) = 0) \Rightarrow (0 \le \operatorname{Complex.re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(v\right), \operatorname{Matrix.mulVec}\left(fun (p: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto fun (q: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto L\left(\operatorname{Matrix.single}\left(p.2, q.2, 1\right), p.1, q.1\right), v\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.CondCP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrikant Utagi and Subhashish Banerjee and R. Srikanth (2024). *On the eternal non-Markovianity of non-unital quantum channels*. DOI: [10.1142/S0219749923500399](https://doi.org/10.1142/S0219749923500399). URL: <https://arxiv.org/abs/2203.10625>.

*Commentary.*

The sum of the diagonal coordinates of v vanishes, so v is orthogonal to the identity vector. The quadratic form uses star v, dotProduct and Matrix.mulVec, followed by Complex.re. The displayed lambda is the output-first coordinate definition of MatrixMap.choi_matrix L: its row p and column q entry is L(Matrix.single p.2 q.2 1)(p.1,q.1). CondCP requires nonnegativity for every such vector.

**Definition 1.5 (A negative generator direction at every positive time).**

$$\forall (Phi: \mathbb{R} \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{EternallyNonMarkovian}\left(Phi\right) = \forall (t: \mathbb{R}), (0 < t) \Rightarrow (\exists (L: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{IsGeneratorAt}\left(Phi, t, L\right)) \land (\neg \operatorname{CondCP}\left(L\right)))$$

*Formalization.* `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.EternallyNonMarkovian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrikant Utagi and Subhashish Banerjee and R. Srikanth (2024). *On the eternal non-Markovianity of non-unital quantum channels*. DOI: [10.1142/S0219749923500399](https://doi.org/10.1142/S0219749923500399). URL: <https://arxiv.org/abs/2203.10625>.

*Commentary.*

At every t > 0 there is a time-local generator L with a negative direction in its conditional Choi form. This is the weak eternal non-Markovianity criterion of a negative canonical rate at every positive time; it imposes no lower bound on the magnitude as t tends to infinity.

**Definition 1.6 (The qubit specialization of the conjecture).**

$$claim = \forall (Phi: \mathbb{R} \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (t: \mathbb{R}), (0 \le t) \Rightarrow (\operatorname{IsCPTP}\left(Phi\left(t\right)\right))) \Rightarrow ((\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), Phi\left(0, X\right) = X) \Rightarrow ((\operatorname{PurelyNonUnital}\left(Phi\right)) \Rightarrow (\neg \operatorname{EternallyNonMarkovian}\left(Phi\right))))$$

*Formalization.* `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.claim` (`✓ std3`).

*Citation.* Shrikant Utagi and Subhashish Banerjee and R. Srikanth (2024). *On the eternal non-Markovianity of non-unital quantum channels*. DOI: [10.1142/S0219749923500399](https://doi.org/10.1142/S0219749923500399). URL: <https://arxiv.org/abs/2203.10625>.

*Commentary.*

Section IV, page 11: "These diverse examples examined in the Section suggest that a purely non-unital channel (i.e., one lacking any unital component) is impossible. Although we have only studied the qubit case, we conjecture that it is true for non-unital channels in arbitrary finite dimensions." Section V, page 11: "However, we conjecture that for a non-unital channel with no such unital component (in the above sense) to be ENM, is impossible." The universal claim here concerns qubits, starts at the identity map, and requires IsCPTP at every nonnegative time. A qubit counterexample refutes the assertion for arbitrary finite dimensions.

**Theorem 1.7 (A rotating replacement counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.result` (`✓ std3`). ∎

*Resolves.* `Problems/utagi-banerjee-srikanth-2024-purely-nonunital-eternal-nonmarkovianity` (refuted) by `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"utagi-banerjee-srikanth-2024-purely-nonunital-eternal-nonmarkovianity","declaration_gid":"D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shrikant Utagi and Subhashish Banerjee and R. Srikanth (2024). *On the eternal non-Markovianity of non-unital quantum channels*. DOI: [10.1142/S0219749923500399](https://doi.org/10.1142/S0219749923500399). URL: <https://arxiv.org/abs/2203.10625>.

*Commentary.*

For real t put D = 1 + t² and P = [[1,t],[t,t²]]/D. The family Phi(t)(X) = (X + t² Matrix.trace(X) P)/D has four Kraus matrices I/D, tI/D, (t/D)[[1,0],[t,0]] and (t/D)[[0,1],[0,t]]. It starts at the identity and is non-unital at every positive time. Its unital part is the isotropic depolarization (X + t² Matrix.trace(X) I/2)/D. For 0 ≤ s ≤ t the intermediate depolarizing parameter is (1+s²)/(1+t²), in [0,1]. Its four Pauli weights are η + (1 − η)/4 and three copies of (1 − η)/4, so it is completely positive and trace preserving. The inverse of Phi(t) sends Y to DY − t² Matrix.trace(Y) P. Composing the derivative with this inverse gives L(Y) = −(2t/D)Y + Matrix.trace(Y) B, where B = [[2t,t²(t²+3)],[t²(t²+3),2t³(t²+2)]]/D³. In the order (0,0),(0,1),(1,0),(1,1), the vector [−2t(t²+3),−t²(t²+3)²,4,2t(t²+3)] has diagonal-coordinate sum zero and conditional Choi quadratic form −2t³(1+t²)(t²+4), strictly negative for t > 0. The replacement direction rotates while the contraction remains a divisible isotropic depolarization.

## References

- Truth anchor: `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.CondCP`
- Truth anchor: `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.EternallyNonMarkovian`
- Truth anchor: `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.IsGeneratorAt`
- Truth anchor: `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.PurelyNonUnital`
- Truth anchor: `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.claim`
- Truth anchor: `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.result`
- Truth anchor: `D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.unitalPart`
- Dependency: [D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound](../Quantum/QuantumChannels/TracePreservingEigenvalueBound.md)
- Dependency: [D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness](PauliThreeWeightBayesianInverseUniqueness.md)
