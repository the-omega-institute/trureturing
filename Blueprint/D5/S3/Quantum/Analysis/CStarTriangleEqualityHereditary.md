# CStarTriangleEqualityHereditary

## Abstract

Triangle equality and norm scale in complex C-star algebras.

**Theorem 1.1 (seminorm algebraically unital rigidity).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] (\exists q \in A,\; \forall a \in A,\; (q \cdot a = a) \land (a \cdot q = a)) \Rightarrow (\forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\exists c \in \operatorname{Real}\left(\right),\; (0 \le c) \land (\forall a \in A,\; p\left(a\right) = c \cdot \left\lVert a \right\rVert)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary.seminorm_algebraically_unital_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Existence of an algebraic two-sided identity suffices for the full seminorm conclusion; the zero algebra is included.

**Theorem 1.2 (seminorm cross scale of continuous).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] \forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\operatorname{Continuous}\left(p\right)) \Rightarrow ((\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\forall a \in A,\; \forall b \in A,\; p\left(a\right) \cdot \left\lVert b \right\rVert = p\left(b\right) \cdot \left\lVert a \right\rVert))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary.seminorm_cross_scale_of_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Joint sandwich approximation places two elements in the same closed subalgebra with a contractive local identity. Continuity then transfers the common scale identity to any pair. No separability or countable approximate unit is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary.seminorm_algebraically_unital_rigidity`
- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary.seminorm_cross_scale_of_continuous`
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityLocalUnitization](CStarTriangleEqualityLocalUnitization.md)
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane](CStarTriangleEqualityPlane.md)
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityUnital](CStarTriangleEqualityUnital.md)
