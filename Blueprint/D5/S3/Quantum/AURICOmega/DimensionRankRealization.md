# Realization of the dimension and feature rank bounds

## Abstract

For natural numbers d and r, three conditions are equivalent: a noncommutative ternary comparison structure of feature rank at most r exists on a preconnected, locally compact space with continuous transfer, each reading kappa x continuous at x, and a neighbourhood of a point mapped continuously and injectively into R^d; such a structure exists on a compact, Hausdorff, connected space with jointly continuous reading and a continuous map into R^d injective on an open set containing the point; and d >= 3 and r >= 5. The unit quaternions realize every such pair.

**Lemma 1.1 (The imaginary part is injective on the closed hemisphere).**

$$\operatorname{InjOn}\left((q: \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)) \mapsto \operatorname{im}\left(q\right), \{q \mid 0 \leq \operatorname{re}\left(q\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/DimensionRankRealization.injOn_im_of_re_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the set of unit quaternions q with 0 <= re q, the map q -> im q is injective. A unit quaternion satisfies re q ^ 2 + imI q ^ 2 + imJ q ^ 2 + imK q ^ 2 = 1. If p and q have the same imaginary part, then re p ^ 2 = re q ^ 2, and since both real parts are nonnegative they are equal; so p = q. In other words, on this closed hemisphere the real part is the nonnegative square root of 1 - |im q| ^ 2. The closed hemisphere cannot be enlarged: a unit quaternion q with re q < 0 has the same imaginary part as the quaternion -re q + im q of the hemisphere.

**Lemma 1.2 (The transfer of the unit quaternion model is continuous).**

$$\operatorname{Continuous}\left((p: \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \times \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \times \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)) \mapsto \operatorname{tri}\left(\operatorname{quaternionModel}, p.1, p.2.1, p.2.2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/DimensionRankRealization.continuous_tri_quaternionModel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transfer of quaternionModel is (x, y, z) -> x * y^-1 * z on the group of unit quaternions. The unit quaternions form a topological group in the subspace topology of the quaternions, so multiplication and inversion are continuous, and the transfer is continuous on the product of three copies of the group.

**Theorem 1.3 (Three equivalent conditions on the pairs of dimension and feature rank).**

$$\forall d, r: \mathbb{N}, \operatorname{TFAE}\left([\exists M: \operatorname{Type}, \exists [\operatorname{TopologicalSpace}\left(M\right)], \exists [\operatorname{LocallyCompactSpace}\left(M\right)], \exists [\operatorname{PreconnectedSpace}\left(M\right)], \exists C: \operatorname{TernaryComparison}\left(M\right), \exists o: M, \exists V: \operatorname{Set}\left(M\right), \exists f: M \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \operatorname{Continuous}\left((p: M \times M \times M) \mapsto \operatorname{tri}\left(C, p.1, p.2.1, p.2.2\right)\right) \land (\forall x: M, \operatorname{ContinuousAt}\left(\operatorname{kappa}\left(C, x\right), x\right)) \land \operatorname{Noncommutative}\left(C\right) \land \operatorname{HasFeatureRank}\left(C, r\right) \land V \in \operatorname{nhds}\left(o\right) \land \operatorname{ContinuousOn}\left(f, V\right) \land \operatorname{InjOn}\left(f, V\right), \exists M: \operatorname{Type}, \exists [\operatorname{TopologicalSpace}\left(M\right)], \exists [\operatorname{CompactSpace}\left(M\right)], \exists [\operatorname{T2Space}\left(M\right)], \exists [\operatorname{ConnectedSpace}\left(M\right)], \exists C: \operatorname{TernaryComparison}\left(M\right), \exists o: M, \exists V: \operatorname{Set}\left(M\right), \exists f: M \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \operatorname{Continuous}\left((p: M \times M \times M) \mapsto \operatorname{tri}\left(C, p.1, p.2.1, p.2.2\right)\right) \land \operatorname{Continuous}\left((p: M \times M) \mapsto \operatorname{kappa}\left(C, p.1, p.2\right)\right) \land \operatorname{Noncommutative}\left(C\right) \land \operatorname{HasFeatureRank}\left(C, r\right) \land \operatorname{IsOpen}\left(V\right) \land o \in V \land \operatorname{Continuous}\left(f\right) \land \operatorname{InjOn}\left(f, V\right), 3 \leq d \land 5 \leq r]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/DimensionRankRealization.exists_model_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d and r be natural numbers. Here C has feature rank r means that the reading kappa x y is the inner product of phi x and phi y for some map phi from M into Euclidean space of dimension r; so it says that C has feature rank at most r. The following three conditions are equivalent. (1) There is a type M in the lowest universe with a topology that is locally compact and preconnected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, such that the transfer (x, y, z) -> tri x y z is continuous on M x M x M, the reading kappa x is continuous at x for every x, C is noncommutative, C has feature rank r, V is a neighbourhood of o, and f is continuous on V and injective on V. (2) There is a type M in the lowest universe with a topology that is compact, Hausdorff and connected, a ternary comparison structure C on M, a point o, a set V and a map f from M into Euclidean space of dimension d, such that the transfer is continuous on M x M x M, the reading (x, y) -> kappa x y is continuous on M x M, C is noncommutative, C has feature rank r, V is open and contains o, f is continuous on M, and f is injective on V. (3) d >= 3 and r >= 5. Condition (2) implies condition (1): a compact Hausdorff space is locally compact, a connected space is preconnected, joint continuity of the reading gives continuity of kappa x at x, an open set containing o is a neighbourhood of o, and a continuous map is continuous on V. Condition (1) implies condition (3) by the dimension and feature rank bound for such structures, theorem three_le_dim_of_hasFeatureRank. For condition (3) implies condition (2) write d = 3 + m. The unit quaternions with the transfer x * y^-1 * z and the reading (1 + <x, y>) / 2 form a noncommutative structure of feature rank five, hence of feature rank at most r for every r >= 5, since feature rank is monotone. The unit quaternions are the unit sphere of the quaternions, so they are compact, Hausdorff, and connected. The transfer is continuous by the lemma above, and the reading is continuous by the lemma that the reading of the unit quaternion model is continuous. Take o = 1, take for V the open hemisphere of unit quaternions of positive real part, an open set containing 1, and take for f the map sending q to its three imaginary coordinates followed by m zero coordinates. This map is continuous on all unit quaternions, and it is injective on V because V lies in the closed hemisphere, on which the imaginary part is injective. So the bounds d >= 3 and r >= 5 are attained, and they are attained already in the more restrictive class of condition (2). The result is assembled from classical facts (the unit three-sphere is a compact connected group, and the hemisphere of nonnegative real part is the graph of a function of the imaginary part) together with the bounds proved in this library; no novelty is claimed. Not stated here: which other structures realize a given pair (d, r); any manifold structure on the unit quaternions; and examples showing that individual hypotheses of the dimension and feature rank bound cannot be dropped.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/DimensionRankRealization.continuous_tri_quaternionModel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/DimensionRankRealization.exists_model_tfae`
- Truth anchor: `D5/S3/Quantum/AURICOmega/DimensionRankRealization.injOn_im_of_re_nonneg`
- Dependency: [D5/S3/Quantum/AURICOmega/FiniteRankDimensionBound](FiniteRankDimensionBound.md)
- Dependency: [D5/S3/Quantum/AURICOmega/GramRankFeatureMap](GramRankFeatureMap.md)
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
- Dependency: [D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup](UnitQuaternionClosedSubgroup.md)
