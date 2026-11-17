# CStarTriangleEqualityNonunitalContinuity

## Abstract

Triangle equality and norm scale in complex C-star algebras.

**Theorem 1.1 (seminorm nonunital lipschitz).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] (\neg (\exists q \in A,\; \forall a \in A,\; (q \cdot a = a) \land (a \cdot q = a))) \Rightarrow (\forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{TEAPair}\left(a, b\right)) \Rightarrow (p\left(a + b\right) = p\left(a\right) + p\left(b\right))) \Rightarrow (\exists C \in \operatorname{NNReal}\left(\right),\; \operatorname{LipschitzWith}\left(C, p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityNonunitalContinuity.seminorm_nonunital_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Without an algebraic two-sided identity, every finite complex TEA-additive seminorm is Lipschitz. Three real spectral values provide disjoint cutoffs, and the nine-corner estimate gives a global bound.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityNonunitalContinuity.seminorm_nonunital_lipschitz`
- Dependency: [D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane](CStarTriangleEqualityPlane.md)
