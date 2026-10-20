# Absolute continuity and accumulated metric variation

## Abstract

Absolute continuity of accumulated metric variation and its exact interval increments.

Let X be an arbitrary metric space, let T be positive, and let z from the real line to X be absolutely continuous on [0,T]. Define A(t) as variationOnFromTo z (Icc 0 T) 0 t. Then A is absolutely continuous on [0,T], and A(b)-A(a) is the real value of the extended metric variation of z on [a,b] for every 0 ≤ a ≤ b ≤ T.

**Theorem 1.1 (Absolute continuity gives bounded metric variation).**

$$\forall Y: Type, \forall metric: \operatorname{PseudoMetricSpace}\left(Y\right), \forall f: \operatorname{RealTo}\left(Y\right), \forall a: Real, \forall b: Real, \operatorname{Implies}\left(\operatorname{AbsolutelyContinuousOnInterval}\left(f, a, b\right), \operatorname{BoundedVariationOn}\left(f, \operatorname{uIcc}\left(a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_boundedVariationOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any pseudometric space Y, any real endpoints a and b, and any f from the real line to Y, absolute continuity on the unordered interval implies bounded variation there. This auxiliary proof reuses the partition argument of Mathlib's AbsolutelyContinuousOnInterval.boundedVariationOn at revision 56a005855ea17e0b0958f73ec801ae140b0a1679. It subdivides the interval into finitely many pieces shorter than an absolute-continuity modulus, bounds every partition sum on each piece, and adds the finite variations. The auxiliary result is used in both the increment identity and the proof of absolute continuity of A.

**Theorem 1.2 (Exact increments of accumulated variation).**

$$\forall X: Type, \forall metric: \operatorname{MetricSpace}\left(X\right), \forall z: \operatorname{RealTo}\left(X\right), \forall T: Real, \operatorname{Implies}\left(\operatorname{LT}\left(0, T\right), \operatorname{Implies}\left(\operatorname{AbsolutelyContinuousOnInterval}\left(z, 0, T\right), \forall a: Real, \forall b: Real, \operatorname{Implies}\left(\operatorname{And}\left(\operatorname{Mem}\left(a, \operatorname{Icc}\left(0, T\right)\right), \operatorname{And}\left(\operatorname{Mem}\left(b, \operatorname{Icc}\left(0, T\right)\right), \operatorname{LE}\left(a, b\right)\right)\right), \operatorname{Eq}\left(\operatorname{Sub}\left(\operatorname{Apply}\left(\operatorname{variationOnFromTo}\left(z, \operatorname{Icc}\left(0, T\right), 0\right), b\right), \operatorname{Apply}\left(\operatorname{variationOnFromTo}\left(z, \operatorname{Icc}\left(0, T\right), 0\right), a\right)\right), \operatorname{ToReal}\left(\operatorname{eVariationOn}\left(z, \operatorname{Icc}\left(a, b\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_variation_exact_increments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bounded variation supplies the finiteness required by variationOnFromTo.sub_right. Subtracting A(a) from A(b) gives variationOnFromTo z (Icc 0 T) a b; variationOnFromTo.eq_of_le identifies this with the real variation on Icc 0 T intersect Icc a b. Since 0 ≤ a ≤ b ≤ T, this intersection is Icc a b. This identity is consumed in the proof that A is absolutely continuous.

**Theorem 1.3 (The variation primitive is absolutely continuous).**

$$\forall X: Type, \forall metric: \operatorname{MetricSpace}\left(X\right), \forall z: \operatorname{RealTo}\left(X\right), \forall T: Real, \operatorname{Implies}\left(\operatorname{LT}\left(0, T\right), \operatorname{Implies}\left(\operatorname{AbsolutelyContinuousOnInterval}\left(z, 0, T\right), \operatorname{AbsolutelyContinuousOnInterval}\left(\operatorname{variationOnFromTo}\left(z, \operatorname{Icc}\left(0, T\right), 0\right), 0, T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_implies_AC_variation_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive epsilon and choose the absolute-continuity modulus of z at epsilon/2. For a finite disjoint family of intervals of total length below that modulus, choose an arbitrary monotone partition inside each interval. Index all partition segments by the dependent finite sum of their segment indices. Within one interval, monotonicity makes the half-open segments disjoint; across different intervals, containment in the original disjoint family gives disjointness. Their lengths telescope in each interval, so the flattened family's total length is bounded by the original total length. The finite-family absolute-continuity estimate therefore bounds the sum of all image segment distances by epsilon/2. The private refinement_bound constructs this family; ac_finite_family reindexes it through a finite enumeration. Taking the finitely many partition suprema with finite_sup_bound bounds the sum of interval variations. Their finiteness permits passage to real values. The exact increment identity turns these real variations into the endpoint distances of A, whose sum is less than epsilon. Thus the argument estimates the actual accumulated variation, for every such disjoint family, throughout the original metric-space telescope.

## References

- Truth anchor: `D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_boundedVariationOn`
- Truth anchor: `D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_implies_AC_variation_primitive`
- Truth anchor: `D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_variation_exact_increments`
