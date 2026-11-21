# Realization of the dimension and feature rank bounds

## Abstract

A noncommutative ternary comparison structure of feature rank r on a preconnected, locally compact space with continuous transfer, each reading kappa x continuous at x, and a neighbourhood of a point mapped continuously and injectively into R^d exists exactly when d >= 3 and r >= 5; every such pair is realized by the unit quaternions.

**Lemma 1.1 (The imaginary part is injective on the open hemisphere).**

$$\operatorname{InjOn}\left((q: \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)) \mapsto \operatorname{im}\left(q\right), \{q \mid 0 < \operatorname{re}\left(q\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/DimensionRankRealization.injOn_im_of_re_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the set of unit quaternions q with re q > 0, the map q -> im q is injective. A unit quaternion satisfies re q ^ 2 + imI q ^ 2 + imJ q ^ 2 + imK q ^ 2 = 1. If p and q have the same imaginary part, then re p ^ 2 = re q ^ 2, and since both real parts are positive they are equal; so p = q. In other words, on this open hemisphere the real part is the positive square root of 1 - |im q| ^ 2.

**Lemma 1.2 (The transfer of the unit quaternion model is continuous).**

$$\operatorname{Continuous}\left((p: \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \times \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \times \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)) \mapsto \operatorname{tri}\left(\operatorname{quaternionModel}, p.1, p.2.1, p.2.2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/DimensionRankRealization.continuous_tri_quaternionModel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transfer of quaternionModel is (x, y, z) -> x * y^-1 * z on the group of unit quaternions. The unit quaternions form a topological group in the subspace topology of the quaternions, so multiplication and inversion are continuous, and the transfer is continuous on the product of three copies of the group.

**Lemma 1.3 (The reading of the unit quaternion model is continuous).**

$$\operatorname{Continuous}\left((p: \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \times \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)) \mapsto \operatorname{kappa}\left(\operatorname{quaternionModel}, p.1, p.2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/DimensionRankRealization.continuous_kappa_quaternionModel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reading of quaternionModel is (x, y) -> (1 + <x, y>) / 2, where <x, y> is the real inner product of the quaternions. The inclusion of the unit quaternions into the quaternions is continuous and the real inner product is continuous, so the reading is continuous on pairs of unit quaternions.

**Theorem 1.4 (The pairs of dimension and feature rank that occur).**

$$\forall d, r: \mathbb{N}, (\exists M: \operatorname{Type}, \exists [\operatorname{TopologicalSpace}\left(M\right)], \exists [\operatorname{LocallyCompactSpace}\left(M\right)], \exists [\operatorname{PreconnectedSpace}\left(M\right)], \exists C: \operatorname{TernaryComparison}\left(M\right), \exists o: M, \exists V: \operatorname{Set}\left(M\right), \exists f: M \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \operatorname{Continuous}\left((p: M \times M \times M) \mapsto \operatorname{tri}\left(C, p.1, p.2.1, p.2.2\right)\right) \land (\forall x: M, \operatorname{ContinuousAt}\left(\operatorname{kappa}\left(C, x\right), x\right)) \land \operatorname{Noncommutative}\left(C\right) \land \operatorname{HasFeatureRank}\left(C, r\right) \land V \in \operatorname{nhds}\left(o\right) \land \operatorname{ContinuousOn}\left(f, V\right) \land \operatorname{InjOn}\left(f, V\right)) \iff (3 \leq d \land 5 \leq r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/DimensionRankRealization.exists_model_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d and r be natural numbers. There is a type M in the lowest universe with a topology that is locally compact and preconnected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, such that the transfer (x, y, z) -> tri x y z is continuous on M x M x M, the reading kappa x is continuous at x for every x, C is noncommutative, C has feature rank r, V is a neighbourhood of o, and f is continuous and injective on V, if and only if d >= 3 and r >= 5. The forward implication is the dimension and feature rank bound for such structures, theorem three_le_dim_of_hasFeatureRank. For the converse write d = 3 + m. The unit quaternions with the transfer x * y^-1 * z and the reading (1 + <x, y>) / 2 form a noncommutative structure of feature rank five, hence of every feature rank r >= 5, since feature rank is monotone. The unit quaternions are the unit sphere of the quaternions, so they are compact, hence locally compact, and preconnected. Transfer and reading are continuous by the two lemmas above. Take o = 1, take for V the open hemisphere of unit quaternions of positive real part, a neighbourhood of 1, and take for f the map sending q to its three imaginary coordinates followed by m zero coordinates. This map is continuous, and it is injective on V by the injectivity of the imaginary part on the open hemisphere. The result is assembled from classical facts (the unit three-sphere is a compact connected group, and the hemisphere of positive real part is the graph of a function of the imaginary part) together with the bounds proved in this library; no novelty is claimed. Not stated here: which other structures realize a given pair (d, r); any manifold structure on the unit quaternions; and the examples showing that the hypotheses of the dimension and feature rank bound cannot be dropped, apart from the realizing model itself.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/DimensionRankRealization.continuous_kappa_quaternionModel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/DimensionRankRealization.continuous_tri_quaternionModel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/DimensionRankRealization.exists_model_iff`
- Truth anchor: `D5/S3/Quantum/AURICOmega/DimensionRankRealization.injOn_im_of_re_pos`
- Dependency: [D5/S3/Quantum/AURICOmega/FiniteRankDimensionBound](FiniteRankDimensionBound.md)
- Dependency: [D5/S3/Quantum/AURICOmega/GramRankFeatureMap](GramRankFeatureMap.md)
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
