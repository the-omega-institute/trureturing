# CStarTriangleEqualityPreservers

## Abstract

Triangle equality and norm scale in complex C-star algebras.

**Definition 1.1 (PreservesTEABothDirections).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), A\right)] \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(B\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), B\right)] \forall T \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), A, B\right),\; \operatorname{PreservesTEABothDirections}\left(T\right) = \left(\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Leftrightarrow (\operatorname{TEAPair}\left(T\left(a\right), T\left(b\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.PreservesTEABothDirections` (`✓ std3`).

*Citation.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Problem 1.1, page 4: Does the same conclusion hold for arbitrary complex C∗-algebras if TEA pairs are preserved in both directions? Both directions here quantify over every pair in the domain.

**Definition 1.2 (ScalarMultipleOfIsometry).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), A\right)] \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(B\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), B\right)] \forall T \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), A, B\right),\; \operatorname{ScalarMultipleOfIsometry}\left(T\right) = \left(\exists gamma \in \operatorname{Complex}\left(\right),\; \exists U \in \operatorname{LinearIsometryEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), A, B\right),\; (gamma \ne 0) \land (\forall a \in A,\; T\left(a\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(gamma, U\left(a\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.ScalarMultipleOfIsometry` (`✓ std3`).

*Citation.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Problem 1.1, page 4: For which complex C∗-algebras 𝒜, ℬ must every linear bijection T : 𝒜 → ℬ preserving parallelism in both directions be a scalar multiple of an isometry? Does the same conclusion hold for arbitrary complex C∗-algebras if TEA pairs are preserved in both directions? The scalar gamma is nonzero and U is a surjective complex-linear isometry.

**Definition 1.3 (claim).**

$$\operatorname{claim}\left(\right) = (\forall A \in \operatorname{Type}\left(\right),\; \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] [\operatorname{NonUnitalCStarAlgebra}\left(B\right)] \forall T \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), A, B\right),\; (\operatorname{Function}.\operatorname{Bijective}\left(T\right)) \Rightarrow ((\forall a \in A,\; \forall b \in A,\; (\left\lVert a + b \right\rVert = \left\lVert a \right\rVert + \left\lVert b \right\rVert) \Leftrightarrow (\left\lVert T\left(a\right) + T\left(b\right) \right\rVert = \left\lVert T\left(a\right) \right\rVert + \left\lVert T\left(b\right) \right\rVert)) \Rightarrow (\exists gamma \in \operatorname{Complex}\left(\right),\; \exists U \in \operatorname{LinearIsometryEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), A, B\right),\; (gamma \ne 0) \land (\forall a \in A,\; T\left(a\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(gamma, U\left(a\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.claim` (`✓ std3`).

*Citation.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Problem 1.1, page 4: For which complex C∗-algebras 𝒜, ℬ must every linear bijection T : 𝒜 → ℬ preserving parallelism in both directions be a scalar multiple of an isometry? Does the same conclusion hold for arbitrary complex C∗-algebras if TEA pairs are preserved in both directions? The second sentence is expressed for arbitrary NonUnitalCStarAlgebra carriers A and B and a complex LinearMap T. Function.Bijective supplies both injectivity and surjectivity; no boundedness or continuity is assumed.

**Theorem 1.4 (result).**

$$\forall A \in \operatorname{Type}\left(\right),\; \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] [\operatorname{NonUnitalCStarAlgebra}\left(B\right)] \forall T \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), A, B\right),\; (\operatorname{Function}.\operatorname{Bijective}\left(T\right)) \Rightarrow ((\forall a \in A,\; \forall b \in A,\; (\left\lVert a + b \right\rVert = \left\lVert a \right\rVert + \left\lVert b \right\rVert) \Leftrightarrow (\left\lVert T\left(a\right) + T\left(b\right) \right\rVert = \left\lVert T\left(a\right) \right\rVert + \left\lVert T\left(b\right) \right\rVert)) \Rightarrow (\exists gamma \in \operatorname{Complex}\left(\right),\; \exists U \in \operatorname{LinearIsometryEquiv}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), A, B\right),\; (gamma \ne 0) \land (\forall a \in A,\; T\left(a\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(gamma, U\left(a\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-ltww2611tea` (proved) by `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-ltww2611tea","declaration_gid":"D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

A finite complex seminorm additive on original TEA pairs is a nonnegative scalar times the original norm. Applying this to a↦‖T(a)‖, injectivity gives a positive scale on a nonzero algebra and surjectivity gives the isometric equivalence. The zero-algebra case uses scalar one. The argument uses forward preservation; the displayed conclusion retains both directions as in Problem 1.1.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.PreservesTEABothDirections`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.ScalarMultipleOfIsometry`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.claim`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.result`
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary](CStarTriangleEqualityHereditary.md)
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityNonunitalContinuity](CStarTriangleEqualityNonunitalContinuity.md)
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane](CStarTriangleEqualityPlane.md)
