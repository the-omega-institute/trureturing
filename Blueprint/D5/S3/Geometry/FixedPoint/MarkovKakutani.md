# Markov-Kakutani common fixed point theorem

## Abstract

Commuting continuous affine self-maps of a compact convex set have a common fixed point.

**Theorem 1.1 (A common fixed point for an arbitrary commuting affine family).**

$$\forall (E: Type*), [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedSpace}(\mathbb{R}, E)] \forall (K: \operatorname{Set}(E)), \forall (hn: \operatorname{Nonempty}(K)), \forall (hc: \operatorname{IsCompact}(K)), \forall (hv: \operatorname{Convex}(\mathbb{R}, K)), \forall (iota: Type*), \forall (F: iota \to \operatorname{ContinuousAffineMap}(\mathbb{R}, E, E)), \forall (hm: \forall (i: iota), \operatorname{MapsTo}(\operatorname{F}(i), K, K)), \forall (hcomm: \forall (i: iota), \forall (j: iota), \forall (x: E), \operatorname{F}(i, \operatorname{F}(j, x)) = \operatorname{F}(j, \operatorname{F}(i, x))), \exists (x: E), (x \in K) \land (\forall (i: iota), \operatorname{F}(i, x) = x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FixedPoint/MarkovKakutani.exists_common_fixed_point` (`✓ std3`). ∎

*Citation.* Unattributed source file; copyright Meta Platforms, Inc. and affiliates (2026). *Markov-Kakutani common fixed point theorem in ATLAS Lean*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/FunctionalAnalysis/MarkovKakutani.lean>.

*Commentary.*

Let E be any real normed vector space and K a nonempty compact convex subset. The index type may be empty or infinite. Each F i is a continuous affine map on E that preserves K, and every pair commutes at every point of E. The conclusion gives one point of K fixed by all maps. Neither completeness nor finite dimension is assumed.

For one map T, average the first m iterates of a point of K. Convexity keeps each Cesaro average in K. Affinity and telescoping make its displacement under T equal to the endpoint difference divided by m. Compactness bounds the iterates and supplies a convergent subsequence; the displacement tends to zero, so continuity fixes the limit.

For a finite subfamily, the common fixed locus already obtained is closed and convex. Global commutation makes the next map preserve that locus, so the single-map result extends the fixed family. The finite fixed loci have the finite intersection property inside compact K; their intersection contains a point fixed by every index. The empty index case follows from nonemptiness of K.

This theorem asserts existence only; it supplies no unique point, algorithm or convergence rate.

## References

- Truth anchor: `D5/S3/Geometry/FixedPoint/MarkovKakutani.exists_common_fixed_point`
