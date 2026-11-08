# CStarTriangleEqualityUnitalSpectral

## Abstract

Triangle equality and norm scale in complex C-star algebras.

**Theorem 1.1 (seminorm spectral plane scale).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall h \in A,\; (\operatorname{IsSelfAdjoint}\left(h\right)) \Rightarrow (\forall alpha \in \operatorname{Complex}\left(\right),\; \forall beta \in \operatorname{Complex}\left(\right),\; p\left(\operatorname{HSMul}.\operatorname{hSMul}\left(alpha, 1\right) + \operatorname{HSMul}.\operatorname{hSMul}\left(beta, h\right)\right) = p\left(1\right) \cdot \left\lVert \operatorname{HSMul}.\operatorname{hSMul}\left(alpha, 1\right) + \operatorname{HSMul}.\operatorname{hSMul}\left(beta, h\right) \right\rVert))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Spectral endpoint evaluation identifies the affine span of the identity and any selfadjoint element with a complex sup plane. The seminorm scale there is its value at the identity; no continuity assumption occurs.

**Theorem 1.2 (seminorm unital lipschitz).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\operatorname{LipschitzWith}\left((\operatorname{Subtype}.\operatorname{mk}\left(2 \cdot p\left(1\right), \mathord{\cdot}\right):\operatorname{NNReal}\left(\right)), p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_unital_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

The decomposition into real and imaginary selfadjoint parts gives Lipschitz constant 2 p(1). The NNReal constant is Subtype.mk of 2 p(1); the dot denotes the proof that this value is nonnegative.

**Theorem 1.3 (norm one add skew quadratic).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall h \in A,\; (\operatorname{IsSelfAdjoint}\left(h\right)) \Rightarrow (\forall s \in \operatorname{Real}\left(\right),\; (0 \le \left\lVert 1 + \operatorname{HSMul}.\operatorname{hSMul}\left(s, \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{I}, h\right)\right) \right\rVert - 1) \land (\left\lVert 1 + \operatorname{HSMul}.\operatorname{hSMul}\left(s, \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{I}, h\right)\right) \right\rVert - 1 \le s^{2} \cdot \left\lVert h \right\rVert^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.norm_one_add_skew_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

The norm increment in a skew-adjoint direction lies between zero and s squared times the squared norm of h, for every real s and selfadjoint h.

**Theorem 1.4 (seminorm normal scale).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall a \in A,\; [\operatorname{IsStarNormal}\left(a\right)] p\left(a\right) = p\left(1\right) \cdot \left\lVert a \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_normal_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

For every normal element, spectral norm attainment determines the same scale p(1). The statement includes all unitary elements.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.norm_one_add_skew_quadratic`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_normal_scale`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral.seminorm_unital_lipschitz`
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane](CStarTriangleEqualityPlane.md)
