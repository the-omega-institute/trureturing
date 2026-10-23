# LogScalarCurvatureMonotone

## Abstract

Strict Schur increase of logarithmic simplex scalar curvature.

**Definition 1.1 (claim).**

$$claim \iff (\forall n : \mathbb{N}, ((3 \le n) \to (\forall x y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R}), ((x \in \operatorname{simplex}\left(n\right)) \to ((y \in \operatorname{simplex}\left(n\right)) \to ((\operatorname{moreMixed}\left(x, y\right)) \to (\operatorname{scalInfty}\left(y\right) \le \operatorname{scalInfty}\left(x\right) \land (((\neg (\exists \sigma : \operatorname{Equiv}. \operatorname{Perm}\left((\operatorname{Fin}\left(n\right))\right), (x = (y) \circ (\sigma))))) \to (\operatorname{scalInfty}\left(y\right) < \operatorname{scalInfty}\left(x\right))))))))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Source quotation (arXiv:math-ph/0407007v2, printed p. 11, Conjecture 4.1): Suppose n>2. For the function Scalₚ(·):𝒫¹ₙ → R one has the following properties: - if p ∈ (1,2) then Scalₚ(·) is a strictly Schur-decreasing function; - if p ∈ (2,+∞] then Scalₚ(·) is a strictly Schur-increasing function. Encoding: n is natural, n>2 becomes 3≤n; x and y are positive normalized Fin n real vectors. moreMixed x y means x is more mixed. Only p=∞ is asserted, with equality allowed for permutations.

**Theorem 1.2 (moreMixed_positive_chain).**

$$\forall (n : \mathbb{N}), \forall (x y : (\operatorname{Fin}\left(n\right)) \to \mathbb{R}), (x \in \operatorname{simplex}\left(n\right)) \to (y \in \operatorname{simplex}\left(n\right)) \to \operatorname{moreMixed}\left(x, y\right) \to \operatorname{Relation}.\operatorname{ReflTransGen}\left(\operatorname{PositiveT}, y, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.moreMixed_positive_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Majorization of positive normalized vectors is realized by a finite chain of positive T-transforms, from the less mixed vector to the more mixed vector.

**Theorem 1.3 (result).**

$$\forall n : \mathbb{N}, ((3 \le n) \to (\forall x y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R}), ((x \in \operatorname{simplex}\left(n\right)) \to ((y \in \operatorname{simplex}\left(n\right)) \to ((\operatorname{moreMixed}\left(x, y\right)) \to (\operatorname{scalInfty}\left(y\right) \le \operatorname{scalInfty}\left(x\right) \land (((\neg (\exists \sigma : \operatorname{Equiv}. \operatorname{Perm}\left((\operatorname{Fin}\left(n\right))\right), (x = (y) \circ (\sigma))))) \to (\operatorname{scalInfty}\left(y\right) < \operatorname{scalInfty}\left(x\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.result` (`✓ std3`). ∎

*Resolves.* `Problems/gibilisco-isola-2004-log-geometry-scalar-curvature` (proved) by `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gibilisco-isola-2004-log-geometry-scalar-curvature","declaration_gid":"D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The logarithmic endpoint follows from the geometric power-sum identity, strict pair equalization and a finite positive transfer chain. No finite-p or quantum clause is asserted.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.claim`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.moreMixed_positive_chain`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.result`
- Dependency: [D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality](PairCurvatureInequality.md)
- Dependency: [D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing](PositiveSimplexGeometryAndMixing.md)
