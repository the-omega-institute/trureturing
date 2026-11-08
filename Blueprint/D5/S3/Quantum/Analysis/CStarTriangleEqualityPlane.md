# CStarTriangleEqualityPlane

## Abstract

Triangle equality and norm scale in complex C-star algebras.

**Definition 1.1 (NormParallel).**

$$\forall E \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), E\right)] \forall a \in E,\; \forall b \in E,\; \operatorname{NormParallel}\left(a, b\right) = \left(\exists mu \in \operatorname{Complex}\left(\right),\; (\left\lVert mu \right\rVert = 1) \land (\left\lVert a + \operatorname{HSMul}.\operatorname{hSMul}\left(mu, b\right) \right\rVert = \left\lVert a \right\rVert + \left\lVert b \right\rVert)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.NormParallel` (`✓ std3`).

*Citation.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Page 1: Two elements a, b in a normed space E over 𝔽 = ℝ or ℂ are said to be norm parallel, or simply parallel, if ‖a + λb‖ = ‖a‖ + ‖b‖ for some λ ∈ 𝔽 with |λ| = 1. Here the field is complex, and zero elements are included.

**Definition 1.2 (TEAPair).**

$$\forall E \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(E\right)] \forall a \in E,\; \forall b \in E,\; \operatorname{TEAPair}\left(a, b\right) = (\left\lVert a + b \right\rVert = \left\lVert a \right\rVert + \left\lVert b \right\rVert)$$

*Formalization.* `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.TEAPair` (`✓ std3`).

*Citation.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Page 1: In this case, we write a ∥ b. If this equality holds specifically with λ = 1, then (a, b) is called a triangle equality attaining (TEA) pair. Thus TEAPair means equality in the triangle inequality, with no phase adjustment.

**Definition 1.3 (affineFacePlane).**

$$\forall X \in \operatorname{Type}\left(\right),\; [\operatorname{TopologicalSpace}\left(X\right)] [\operatorname{CompactSpace}\left(X\right)] \forall t \in \operatorname{ContinuousMap}\left(X, \operatorname{Real}\left(\right)\right),\; \forall ht \in \left(\forall x \in X,\; t\left(x\right) \in \operatorname{Set}.\operatorname{Icc}\left(0, 1\right)\right),\; \forall xzero \in X,\; \forall xone \in X,\; \forall hzero \in t\left(xzero\right) = 0,\; \forall hone \in t\left(xone\right) = 1,\; \forall v \in \operatorname{Complex}\left(\right) \times \operatorname{Complex}\left(\right),\; \forall x \in X,\; \operatorname{affineFacePlane}\left(t, ht, xzero, xone, hzero, hone\right)\left(v, x\right) = (1 - (t\left(x\right):\operatorname{Complex}\left(\right))) \cdot \operatorname{Prod}.\operatorname{fst}\left(v\right) + (t\left(x\right):\operatorname{Complex}\left(\right)) \cdot \operatorname{Prod}.\operatorname{snd}\left(v\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.affineFacePlane` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

A continuous real function with values in [0,1] attaining both endpoints defines this complex-linear isometric map from the sup-norm plane into ContinuousMap X Complex. Its value is displayed at every point; ht, hzero and hone are the indicated proofs.

**Theorem 1.4 (seminorm on isometric plane).**

$$\forall F \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), F\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), F\right),\; (\forall a \in F,\; \forall b \in F,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall J \in \operatorname{LinearIsometry}\left(\operatorname{RingHom}.\operatorname{id}\left(\operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right) \times \operatorname{Complex}\left(\right), F\right),\; \forall v \in \operatorname{Complex}\left(\right) \times \operatorname{Complex}\left(\right),\; p\left(J\left(v\right)\right) = p\left(J\left((1,0)\right)\right) \cdot \left\lVert v \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_on_isometric_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Pullback along any complex-linear isometric embedding of the complex sup plane forces a common seminorm scale. The seminorm may vanish, and the embedding need not have an algebraic image.

**Theorem 1.5 (seminorm orthogonal axes).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall a \in A,\; \forall b \in A,\; (\left\lVert a \right\rVert = 1) \Rightarrow ((\left\lVert b \right\rVert = 1) \Rightarrow (((\operatorname{star}\left(a\right) \cdot b = 0) \land (a \cdot \operatorname{star}\left(b\right) = 0)) \Rightarrow (p\left(a\right) = p\left(b\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_orthogonal_axes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Two C-star orthogonal elements of norm one have equal values under a complex seminorm additive on TEA pairs.

**Theorem 1.6 (seminorm orthogonal unit scale).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall x \in A,\; \forall g \in A,\; (\left\lVert g \right\rVert = 1) \Rightarrow ((\operatorname{star}\left(x\right) \cdot g = 0) \Rightarrow ((x \cdot \operatorname{star}\left(g\right) = 0) \Rightarrow (p\left(x\right) = p\left(g\right) \cdot \left\lVert x \right\rVert))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_orthogonal_unit_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

An element orthogonal on both sides to a norm-one element has the scale fixed by that element; the first element may be zero.

**Theorem 1.7 (seminorm product rigidity).**

$$\forall E \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), E\right)] \forall F \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(\operatorname{Complex}\left(\right), F\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), E \times F\right),\; (\forall a \in E \times F,\; \forall b \in E \times F,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall ezero \in E,\; \forall fzero \in F,\; (\left\lVert ezero \right\rVert = 1) \Rightarrow ((\left\lVert fzero \right\rVert = 1) \Rightarrow (\forall v \in E \times F,\; p\left(v\right) = p\left((ezero,0)\right) \cdot \left\lVert v \right\rVert)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_product_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

A finite complex seminorm additive on TEA pairs of a sup product has one norm scale when both factors contain a unit vector. The scale can be zero.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.NormParallel`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.TEAPair`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.affineFacePlane`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_on_isometric_plane`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_orthogonal_axes`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_orthogonal_unit_scale`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane.seminorm_product_rigidity`
