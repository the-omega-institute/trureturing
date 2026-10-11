# PositiveSimplexGeometryAndMixing

## Abstract

Logarithmic simplex curvature formula and positive T-transform chain.

**Definition 1.1 (simplex).**

$$\forall (n : \mathbb{N}), \operatorname{simplex}\left(n\right) = (\{(x : \operatorname{Fin}\left(n\right) \to \mathbb{R}) | ((\forall i , (0 < x\left(i\right))) \land (\sum_{i} (x\left(i\right)) = 1))\})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.simplex` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Source definition (printed p. 3, Definition 2.1): 𝒫¹ₙ := {ρ ∈ ℝⁿ | ∑ᵢ ρᵢ=1, ρᵢ>0}. Fin n indexes these n coordinates from zero.

**Definition 1.2 (chart).**

$$\forall (n : \mathbb{N}), \forall (t : (\operatorname{Fin}\left((n - 1)\right)) \to (\mathbb{R})), \operatorname{chart}\left(t\right) = (\operatorname{fun} k \mapsto (\operatorname{if} (h : \operatorname{val}\left(k\right) < n - 1) \operatorname{then} (t\left(\langle \operatorname{val}\left(k\right), h \rangle\right)) \operatorname{else} (1 - \sum_{i} (t\left(i\right)))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

This affine simplex chart uses the first n−1 coordinates and fills the final coordinate by one minus their sum. The branch proof supplies the Fin index.

**Definition 1.3 (metric).**

$$\forall (n : \mathbb{N}), \forall (t : (\operatorname{Fin}\left((n - 1)\right)) \to (\mathbb{R})), \operatorname{metric}\left(t\right) = (\operatorname{fun} i j \mapsto (\sum_{k} ((\operatorname{fderiv}\left(\mathbb{R}, (\operatorname{fun} s \mapsto (\operatorname{Real}. \operatorname{log}\left((\operatorname{chart}\left(s, k\right))\right))), t, (\operatorname{Pi}. \operatorname{single}\left(i, 1\right))\right)) \cdot (\operatorname{fderiv}\left(\mathbb{R}, (\operatorname{fun} s \mapsto (\operatorname{Real}. \operatorname{log}\left((\operatorname{chart}\left(s, k\right))\right))), t, (\operatorname{Pi}. \operatorname{single}\left(j, 1\right))\right)))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.metric` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Source quotation (printed p. 10, Definition 4.3): The α-geometry on 𝒫¹ₙ is the pull-back geometry induced by the map Aₚ(ρ):𝒫¹ₙ → ℝⁿ defined by Aₚ(ρ):=pρ¹⁄ᵖ for p∈ℝ∖{0}, log(ρ) for p=∞, where p=2/(1−α). At the logarithmic endpoint the displayed Euclidean pull-back metric uses Fréchet derivatives and coordinate directions.

**Definition 1.4 (christoffel).**

$$\forall (n : \mathbb{N}), \forall (t : (\operatorname{Fin}\left((n - 1)\right)) \to (\mathbb{R})), \forall (k : \operatorname{Fin}\left((n - 1)\right)), \forall (i : \operatorname{Fin}\left((n - 1)\right)), \forall (j : \operatorname{Fin}\left((n - 1)\right)), \operatorname{christoffel}\left(t, k, i, j\right) = ((((1) / (2)) : (\mathbb{R})) \cdot \sum_{l} (\left(((\operatorname{metric}\left(t\right)))^{-1}\right)\left(k, l\right) \cdot (\operatorname{fderiv}\left(\mathbb{R}, (\operatorname{fun} s \mapsto (\operatorname{metric}\left(s, l, j\right))), t, (\operatorname{Pi}. \operatorname{single}\left(i, 1\right))\right) + \operatorname{fderiv}\left(\mathbb{R}, (\operatorname{fun} s \mapsto (\operatorname{metric}\left(s, l, i\right))), t, (\operatorname{Pi}. \operatorname{single}\left(j, 1\right))\right) - \operatorname{fderiv}\left(\mathbb{R}, (\operatorname{fun} s \mapsto (\operatorname{metric}\left(s, i, j\right))), t, (\operatorname{Pi}. \operatorname{single}\left(l, 1\right))\right))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.christoffel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The Levi-Civita Christoffel symbols are defined from the inverse metric and the three metric derivatives, with coefficient one half.

**Definition 1.5 (ricci).**

$$\forall (n : \mathbb{N}), \forall (t : (\operatorname{Fin}\left((n - 1)\right)) \to (\mathbb{R})), \forall (i : \operatorname{Fin}\left((n - 1)\right)), \forall (j : \operatorname{Fin}\left((n - 1)\right)), \operatorname{ricci}\left(t, i, j\right) = (\sum_{k} ((\operatorname{fderiv}\left(\mathbb{R}, (\operatorname{fun} s \mapsto (\operatorname{christoffel}\left(s, k, i, j\right))), t, (\operatorname{Pi}. \operatorname{single}\left(k, 1\right))\right) - \operatorname{fderiv}\left(\mathbb{R}, (\operatorname{fun} s \mapsto (\operatorname{christoffel}\left(s, k, i, k\right))), t, (\operatorname{Pi}. \operatorname{single}\left(j, 1\right))\right) + (\sum_{l} ((\operatorname{christoffel}\left(t, k, k, l\right) \cdot \operatorname{christoffel}\left(t, l, i, j\right) - \operatorname{christoffel}\left(t, k, j, l\right) \cdot \operatorname{christoffel}\left(t, l, i, k\right)))))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.ricci` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The Ricci contraction uses the displayed derivative order and Christoffel products.

**Definition 1.6 (scalarCurvature).**

$$\forall (n : \mathbb{N}), \forall (t : (\operatorname{Fin}\left((n - 1)\right)) \to (\mathbb{R})), \operatorname{scalarCurvature}\left(t\right) = (\sum_{i} (\sum_{j} (\left(((\operatorname{metric}\left(t\right)))^{-1}\right)\left(i, j\right) \cdot \operatorname{ricci}\left(t, i, j\right))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.scalarCurvature` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Source quotation (printed p. 10, Definition 4.4): We denote by Scalₚ(ρ) the scalar curvature of the α-geometry (with p=2/(1−α)) at the point ρ∈𝒫¹ₙ. The displayed coordinate definition contracts the inverse metric with the Ricci tensor.

**Definition 1.7 (scalInfty).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \operatorname{scalInfty}\left(x\right) = \operatorname{scalarCurvature}\left((\operatorname{fun} i \mapsto x\left((\operatorname{Fin}.\operatorname{castLE}\left((\operatorname{Nat.sub_{le}}\left(n, 1\right)), i\right))\right))\right)$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.scalInfty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The first n−1 coordinates are restricted by Fin.castLE (Nat.sub_le n 1). Nat subtraction is truncated subtraction.

**Definition 1.8 (desc).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \operatorname{desc}\left(x\right) = (((\operatorname{List}. \operatorname{ofFn}\left(x\right))). \operatorname{mergeSort}\left((\operatorname{fun} a b \mapsto (\operatorname{decide}\left((b \le a)\right)))\right))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Decreasing merge-sort arranges all coordinates from largest to smallest.

**Definition 1.9 (prefixSum).**

$$\forall (xs : \operatorname{List}\left(\mathbb{R}\right)), \forall (k : \mathbb{N}), \operatorname{prefixSum}\left(xs, k\right) = (((xs. \operatorname{take}\left(k\right))). \operatorname{sum})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.prefixSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The list initial sum is the sum of its first k entries.

**Definition 1.10 (moreMixed).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \operatorname{moreMixed}\left(x, y\right) \iff ((\forall k < n, (\operatorname{prefixSum}\left((\operatorname{desc}\left(x\right)), k\right) \le \operatorname{prefixSum}\left((\operatorname{desc}\left(y\right)), k\right))) \land \operatorname{prefixSum}\left((\operatorname{desc}\left(x\right)), n\right) = \operatorname{prefixSum}\left((\operatorname{desc}\left(y\right)), n\right))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Source quotation (printed p. 3, Definition 2.3): “x is more mixed (more chaotic,...) than y (denoted by x ≻ y) if and only if” followed by the source’s decreasing initial-sum inequalities and total-sum equality. Encoding: the inequalities hold for k<n and equality at k=n. Fin n uses zero-based indices; a prefix of length k still contains k coordinates.

**Definition 1.11 (remain).**

$$\forall (m : \mathbb{N}), \forall (t : (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), \operatorname{remain}\left(t\right) = (1 - \sum_{i} (t\left(i\right)))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.remain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The final chart coordinate is one minus the sum of the independent coordinates.

**Definition 1.12 (chartDomain).**

$$\forall (m : \mathbb{N}), \operatorname{chartDomain}\left(m\right) = (\{(t : \operatorname{Fin}\left(m\right) \to \mathbb{R}) | ((\forall i , (0 < t\left(i\right))) \land (\sum_{i} (t\left(i\right)) < 1))\})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chartDomain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The independent chart coordinates are positive and have sum below one.

**Lemma 1.13 (chart_castSucc).**

$$\forall (m : \mathbb{N}), \forall (t : (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), \forall (i : \operatorname{Fin}\left(m\right)), \left(\operatorname{chart}_{(m + 1)}\right)\left(t, i. \operatorname{castSucc}\right) = t\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chart_castSucc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

At dimension m+1 the first m chart coordinates are the given coordinates.

**Lemma 1.14 (chart_last).**

$$\forall (m : \mathbb{N}), \forall (t : (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), \left(\operatorname{chart}_{(m + 1)}\right)\left(t, (\operatorname{Fin}. \operatorname{last}\left(m\right))\right) = \operatorname{remain}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chart_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

At dimension m+1 the last chart coordinate is remain.

**Definition 1.15 (chartS2).**

$$\forall (m : \mathbb{N}), \forall (t : (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), \operatorname{chartS2}\left(t\right) = ((\operatorname{remain}\left(t\right))^{2} + \sum_{i} ((t\left(i\right))^{2}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chartS2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The full simplex square sum consists of the square of remain and the square sum of the independent coordinates.

**Lemma 1.16 (chartS2_pos).**

$$\forall (m : \mathbb{N}), \forall (t : (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), (t \in \operatorname{chartDomain}\left(m\right)) \Rightarrow (0 < \operatorname{chartS2}\left(t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chartS2_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The positive final chart coordinate makes the full square sum positive.

**Lemma 1.17 (scalarCurvature_powerSums).**

$$\forall (m : \mathbb{N}), \forall (t : (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), (t \in \operatorname{chartDomain}\left(m\right)) \Rightarrow (\left(\operatorname{scalarCurvature}_{(m + 1)}\right)\left(t\right) = ((((\sum_{i} (t\left(i\right))))^{2} - (\sum_{i} ((t\left(i\right))^{2})) - (2 \cdot (\sum_{i} (t\left(i\right))) \cdot (\sum_{i} ((t\left(i\right))^{2} \cdot (t\left(i\right) - \operatorname{remain}\left(t\right))))) / (\operatorname{chartS2}\left(t\right)) + (2 \cdot (\sum_{i} ((t\left(i\right))^{3} \cdot (t\left(i\right) - \operatorname{remain}\left(t\right))))) / (\operatorname{chartS2}\left(t\right)))) / (\operatorname{chartS2}\left(t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.scalarCurvature_powerSums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The coordinate calculation reduces the scalar curvature to finite power sums. The diagonal-plus-rank-one inverse uses the pinned Mathlib Woodbury identity.

**Definition 1.18 (PositiveT).**

$$\forall (n : \mathbb{N}), \forall (y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (q : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \operatorname{PositiveT}\left(y, q\right) \iff (\operatorname{IsTTransform}\left(y, q\right) \land \left((\forall i , (0 < y\left(i\right))) \land \left((\forall i , (0 < q\left(i\right))) \land (\sum_{i} (q\left(i\right))) = \sum_{i} (y\left(i\right))\right)\right))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.PositiveT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

A positive T-transform preserves the coordinate sum and has positive endpoints.

**Lemma 1.19 (ttransform_positive).**

$$\forall (n : \mathbb{N}), \forall (y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (q : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\operatorname{IsTTransform}\left(y, q\right)) \Rightarrow ((\forall i , (0 < y\left(i\right))) \Rightarrow (\forall i , (0 < q\left(i\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.ttransform_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

A convex mixture of a positive vector and its coordinate swap remains positive.

**Lemma 1.20 (ttransform_sum).**

$$\forall (n : \mathbb{N}), \forall (y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (q : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\operatorname{IsTTransform}\left(y, q\right)) \Rightarrow ((\sum_{i} (q\left(i\right))) = \sum_{i} (y\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.ttransform_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Mixing with a coordinate swap preserves the coordinate sum.

**Lemma 1.21 (positive_sorted_chain).**

$$\forall (n : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\operatorname{Antitone}\left(z\right)) \Rightarrow ((\forall i , (0 < z\left(i\right))) \Rightarrow ((\forall i , (0 < y\left(i\right))) \Rightarrow ((\forall k , (\operatorname{D5}. \operatorname{S3}. \operatorname{Geometry}. \operatorname{AlphaGeometry}. \operatorname{MajorizationTransfer}. \operatorname{FiniteVector}. \operatorname{prefixSum}\left(k, z\right) \le \operatorname{D5}. \operatorname{S3}. \operatorname{Geometry}. \operatorname{AlphaGeometry}. \operatorname{MajorizationTransfer}. \operatorname{FiniteVector}. \operatorname{prefixSum}\left(k, y\right))) \Rightarrow (((\sum_{i} (z\left(i\right))) = \sum_{i} (y\left(i\right))) \Rightarrow (\operatorname{Relation}. \operatorname{ReflTransGen}\left(\operatorname{PositiveT}, y, z\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.positive_sorted_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Induction on the number of unmatched coordinates iterates the transplanted transfer step. Every step stays positive and preserves the sum.

**Lemma 1.22 (positiveT_simplex).**

$$\forall (n : \mathbb{N}), \forall (y : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), \forall (q : (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\operatorname{PositiveT}\left(y, q\right)) \Rightarrow ((y \in \operatorname{simplex}\left(n\right)) \Rightarrow (q \in \operatorname{simplex}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.positiveT_simplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

A positive T-transform preserves membership in the normalized positive simplex.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.PositiveT`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chart`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chartDomain`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chartS2`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chartS2_pos`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chart_castSucc`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.chart_last`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.christoffel`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.metric`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.positiveT_simplex`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.positive_sorted_chain`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.prefixSum`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.remain`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.ricci`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.scalInfty`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.scalarCurvature`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.scalarCurvature_powerSums`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.simplex`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.ttransform_positive`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.ttransform_sum`
- Dependency: [D5/S3/Geometry/AlphaGeometry/MajorizationTransfer](MajorizationTransfer.md)
