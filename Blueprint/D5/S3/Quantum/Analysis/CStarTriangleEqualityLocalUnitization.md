# CStarTriangleEqualityLocalUnitization

## Abstract

Triangle equality and norm scale in complex C-star algebras.

**Theorem 1.1 (local unitization seminorm scale).**

$$\forall A \in \operatorname{Type}\left(\right),\; \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{NonUnitalCStarAlgebra}\left(A\right)] [\operatorname{NonUnitalCStarAlgebra}\left(B\right)] \forall phi \in \operatorname{NonUnitalStarAlgHom}\left(\operatorname{Complex}\left(\right), B, A\right),\; (\operatorname{Function}.\operatorname{Injective}\left(phi\right)) \Rightarrow ((\neg (\exists q \in B,\; \forall a \in B,\; (q \cdot a = a) \land (a \cdot q = a))) \Rightarrow (\forall e \in A,\; (\left\lVert e \right\rVert \le 1) \Rightarrow ((\forall b \in B,\; e \cdot phi\left(b\right) = phi\left(b\right)) \Rightarrow ((\forall q \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), \operatorname{Unitization}\left(\operatorname{Complex}\left(\right), B\right)\right),\; (\forall x \in \operatorname{Unitization}\left(\operatorname{Complex}\left(\right), B\right),\; \forall y \in \operatorname{Unitization}\left(\operatorname{Complex}\left(\right), B\right),\; (\left\lVert x + y \right\rVert = \left\lVert x \right\rVert + \left\lVert y \right\rVert) \Rightarrow (q\left(x + y\right) = q\left(x\right) + q\left(y\right))) \Rightarrow (\forall x \in \operatorname{Unitization}\left(\operatorname{Complex}\left(\right), B\right),\; q\left(x\right) = q\left(1\right) \cdot \left\lVert x \right\rVert)) \Rightarrow (\forall p \in \operatorname{Seminorm}\left(\operatorname{Complex}\left(\right), A\right),\; (\forall x \in A,\; \forall y \in A,\; (\left\lVert x + y \right\rVert = \left\lVert x \right\rVert + \left\lVert y \right\rVert) \Rightarrow (p\left(x + y\right) = p\left(x\right) + p\left(y\right))) \Rightarrow (\forall b \in B,\; p\left(phi\left(b\right)\right) = p\left(e\right) \cdot \left\lVert b \right\rVert))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CStarTriangleEqualityLocalUnitization.local_unitization_seminorm_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li, Ming-Cheng Tsai, Ya-Shu Wang and Ngai-Ching Wong (2026). *Linear maps of C*-algebras preserving norm parallelism*. DOI: [10.48550/arXiv.2611.06187](https://doi.org/10.48550/arXiv.2611.06187). URL: <https://arxiv.org/abs/2611.06187v1>.

*Commentary.*

Let phi embed a genuinely nonunital complex C-star algebra B into A, and let a contraction e act as a left identity on its image. If every TEA-additive complex seminorm on Unitization Complex B has the unital scale property, then any such seminorm on A has scale p(e) on phi(B). The linear local-unitization map is isometric; multiplicativity of that map is not required.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CStarTriangleEqualityLocalUnitization.local_unitization_seminorm_scale`
