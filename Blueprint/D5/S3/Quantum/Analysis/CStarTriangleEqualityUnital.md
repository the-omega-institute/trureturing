# CStarTriangleEqualityUnital

## Abstract

Triangle equality and norm scale in complex C-star algebras.

**Theorem 1.1 (seminorm unital rigidity).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall a \in A,\; p\left(a\right) = p\left(1\right) \cdot \left\lVert a \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnital.seminorm_unital_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

A finite complex seminorm additive on TEA pairs is p(1) times the original norm on a nonzero unital complex C-star algebra. A spectral real-part lower bound and the Russo-Dye convex-hull theorem give the two inequalities.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityUnital.seminorm_unital_rigidity`
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane](CStarTriangleEqualityPlane.md)
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral](CStarTriangleEqualityUnitalSpectral.md)
- Dependency: [D5/S3/Quantum/Analysis/RussoDye](RussoDye.md)
