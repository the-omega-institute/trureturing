# Complete ternary comparison structures of feature rank five

## Abstract

A noncommutative, chain-connected ternary comparison structure of feature rank five whose reading touches zero and is complete is in bijection with the unit quaternions, by a map that sends a chosen point to 1 and carries its transfer and reading to those of the quaternion comparison model.

**Definition 1.1 (Complete reading).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{ReadingComplete}\left(C\right) \Leftrightarrow \left(\forall x \in \mathbb{N} \to M,\; \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists N \in \mathbb{N},\; \forall m \in \mathbb{N}, n \in \mathbb{N},\; N \le m \Rightarrow \left(N \le n \Rightarrow 1 - e < \operatorname{kappa}\left(C, x\left(m\right), x\left(n\right)\right)\right)\right)\right) \Rightarrow \left(\exists a \in M,\; \forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists N \in \mathbb{N},\; \forall n \in \mathbb{N},\; N \le n \Rightarrow 1 - e < \operatorname{kappa}\left(C, x\left(n\right), a\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.ReadingComplete` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reading of a ternary comparison structure C on M is complete when every sequence x of points of M whose readings kappa(C, x m, x n) exceed 1 - e for all m and n beyond some N, for every e > 0, has a point a whose readings kappa(C, x n, a) with the sequence exceed 1 - e for all n beyond some N, for every e > 0. Reading values close to one play the role of small distances, so this is completeness of M for the closeness measured by the reading. The condition holds for the quaternion comparison model, because its reading is one minus a quarter of the squared distance, 1 - |x - y|^2 / 4, and the unit quaternions are a closed subset of the complete space of quaternions; this consequence is not among the formal statements of the module.

**Lemma 1.2 (The quaternion reading in terms of distance).**

$$\forall a \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), b \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{kappa}\left(\operatorname{quaternionModel}, a, b\right) = 1 - \frac{\operatorname{dist}\left(a, b\right)^{2}}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.kappa_eq_one_sub_dist_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit quaternions a and b, the reading of the quaternion comparison model is (1 + <a, b>) / 2, where <a, b> is the real inner product. Since |a - b|^2 = |a|^2 - 2 <a, b> + |b|^2 and both norms are one, <a, b> = 1 - |a - b|^2 / 2, and the reading is 1 - |a - b|^2 / 4. Here dist(a, b) is the distance |a - b| of a and b as quaternions.

**Lemma 1.3 (A normalized embedding into the unit quaternions).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{Noncommutative}\left(C\right) \Rightarrow \left(\operatorname{ChainConnected}\left(C\right) \Rightarrow \left(\operatorname{TouchesZero}\left(C\right) \Rightarrow \left(\operatorname{HasFeatureRank}\left(C, 5\right) \Rightarrow \left(\forall o \in M,\; \exists v \in M \to \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{Injective}\left(v\right) \land \left(v\left(o\right) = 1 \land \left(\left(\forall x \in M, y \in M, z \in M,\; v\left(\operatorname{tri}\left(C, x, y, z\right)\right) = v\left(x\right) \cdot v\left(y\right)^{-1} \cdot v\left(z\right)\right) \land \left(\forall x \in M, y \in M,\; \operatorname{kappa}\left(C, x, y\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, v\left(x\right), v\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.exists_normalized_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a ternary comparison structure on M whose transfer is order sensitive and whose reading is chain connected, takes values arbitrarily close to zero and is the Gram kernel of a map into Euclidean 5-space, and let o be a point of M. Then there is an injective map v from M into the unit quaternions with v(o) = 1 that carries the transfer to v(tri(C, x, y, z)) = v(x) * v(y)^-1 * v(z) and preserves the reading, kappa(C, x, y) = kappa(quaternionModel, v(x), v(y)). The feature-rank embedding gives an injective map w with the same transfer law and with kappa(C, x, y) = (1 + <w(x), w(y)>) / 2. The map v(x) = w(o)^-1 * w(x) is injective and sends o to 1; the transfer law follows from the group identity (w(o)^-1 * p) * (w(o)^-1 * q)^-1 * (w(o)^-1 * r) = w(o)^-1 * (p * q^-1 * r), and the reading is preserved because left multiplication by a unit quaternion preserves the real inner product.

**Definition 1.4 (The image as a subgroup).**

Lean statement: `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.rangeSubgroup`

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.rangeSubgroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let C be a ternary comparison structure on M, o a point of M and v a map from M into the unit quaternions with v(o) = 1 and v(tri(C, x, y, z)) = v(x) * v(y)^-1 * v(z) for all x, y and z. The image of v is then a subgroup of the unit quaternions: it contains v(o) = 1, the product v(x) * v(y) is the image v(tri(C, x, o, y)), and the inverse of v(x) is the image v(tri(C, o, x, o)). This definition records the image of v with that subgroup structure.

**Lemma 1.5 (Under a complete reading the image is closed).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall v \in M \to \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \left(\forall x \in M, y \in M,\; \operatorname{kappa}\left(C, x, y\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, v\left(x\right), v\left(y\right)\right)\right) \Rightarrow \left(\operatorname{ReadingComplete}\left(C\right) \Rightarrow \operatorname{IsClosed}\left(\operatorname{range}\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.isClosed_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a ternary comparison structure on M with complete reading and let v be a map from M into the unit quaternions with kappa(C, x, y) = kappa(quaternionModel, v(x), v(y)) for all x and y. Then the image of v is a closed subset of the unit quaternions. Let v(x n) converge to a unit quaternion q. The reading between unit quaternions is 1 - dist^2 / 4, so the readings kappa(C, x m, x n) are within e of one for all large m and n, for every e > 0. Completeness gives a point a whose readings kappa(C, x n, a) tend to one; then dist(v(x n), v(a)) tends to zero, so v(x n) converges to v(a), and q = v(a) lies in the image. Sequentially closed subsets of a metric space are closed.

**Theorem 1.6 (Complete structures of feature rank five are the unit quaternions).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{Noncommutative}\left(C\right) \Rightarrow \left(\operatorname{ChainConnected}\left(C\right) \Rightarrow \left(\operatorname{TouchesZero}\left(C\right) \Rightarrow \left(\operatorname{HasFeatureRank}\left(C, 5\right) \Rightarrow \left(\operatorname{ReadingComplete}\left(C\right) \Rightarrow \left(\forall o \in M,\; \exists u \in \operatorname{Equiv}\left(M, \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)\right),\; u\left(o\right) = 1 \land \left(\left(\forall x \in M, y \in M, z \in M,\; u\left(\operatorname{tri}\left(C, x, y, z\right)\right) = \operatorname{tri}\left(\operatorname{quaternionModel}, u\left(x\right), u\left(y\right), u\left(z\right)\right)\right) \land \left(\forall x \in M, y \in M,\; \operatorname{kappa}\left(C, x, y\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, u\left(x\right), u\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.exists_unitQuaternion_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a ternary comparison structure on M whose transfer is order sensitive, whose reading is chain connected, takes values arbitrarily close to zero, is the Gram kernel of a map into Euclidean 5-space, and is complete. Then for every point o of M there is a bijection u from M onto the unit quaternions with u(o) = 1 that carries the transfer of C to the transfer tri(quaternionModel, p, q, r) = p * q^-1 * r of the quaternion comparison model and the reading of C to its reading kappa(quaternionModel, p, q) = (1 + <p, q>) / 2, where <p, q> is the real inner product of quaternions. The feature-rank embedding gives an injective map w from M into the unit quaternions with w(tri(C, x, y, z)) = w(x) * w(y)^-1 * w(z) and kappa(C, x, y) = (1 + <w(x), w(y)>) / 2. The map v(x) = w(o)^-1 * w(x) is injective, sends o to 1, carries the transfer to x * y^-1 * z, and preserves the reading, because left multiplication by a unit quaternion preserves the real inner product. Its image is a subgroup of the unit quaternions: v(x) * v(y) = v(tri(C, x, o, y)) and the inverse of v(x) is v(tri(C, o, x, o)). Between unit quaternions the reading is 1 - |p - q|^2 / 4. Hence if v(x n) converges to a unit quaternion q, the readings kappa(C, x m, x n) tend to one uniformly in m and n, completeness gives a point a whose readings kappa(C, x n, a) tend to one, so v(x n) also converges to v(a), and q = v(a); the image is closed. For every e > 0, a chain of points of M with consecutive readings above 1 - e is carried by v to a chain in the image with the same consecutive readings, and two points that do not commute in the group of C at o, whose product is tri(C, x, o, y), are carried to unit quaternions that do not commute. A closed, noncommutative subgroup of the unit quaternions in which any two elements are joined by such chains is the whole group, so v is a bijection onto the unit quaternions.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.ReadingComplete`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.exists_normalized_embedding`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.exists_unitQuaternion_equiv`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.isClosed_range`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.kappa_eq_one_sub_dist_sq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism.rangeSubgroup`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonRankFive](TernaryComparisonRankFive.md)
- Dependency: [D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup](UnitQuaternionClosedSubgroup.md)
