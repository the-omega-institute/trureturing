# Rank-five ternary comparison structures without completeness

## Abstract

Without completeness of the reading, a noncommutative, chain-connected ternary comparison structure of feature rank five whose reading touches zero embeds into the unit quaternions with dense range; a subgroup of the unit quaternions with the induced structure has complete reading exactly when it is closed, a dense subgroup satisfies the other four hypotheses, and a countable dense subgroup shows that completeness does not follow from them.

**Definition 1.1 (The induced structure on a subgroup of the unit quaternions).**

Lean statement: `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.subgroupModel`

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.subgroupModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let H be a subgroup of the group unitary(H[R]) of unit quaternions. subgroupModel(H) is the ternary comparison structure whose points are the elements of H, whose transfer is tri(x, y, z) = x * y^-1 * z, and whose reading is kappa(x, y) = (1 + <x, y>) / 2, where <x, y> is the real inner product of quaternions. The transfer of three elements of H lies in H because H is closed under products and inverses, and both operations are those of the quaternion comparison model quaternionModel restricted to H. Each identity required of a ternary comparison structure holds in subgroupModel(H) because it holds in quaternionModel; in particular the reading of two elements of H equals one exactly when they are equal, since elements of H are equal exactly when they are equal as unit quaternions.

**Theorem 1.2 (Without completeness, the embedding into the unit quaternions has dense range).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{Noncommutative}\left(C\right) \Rightarrow \left(\operatorname{ChainConnected}\left(C\right) \Rightarrow \left(\operatorname{TouchesZero}\left(C\right) \Rightarrow \left(\operatorname{HasFeatureRank}\left(C, 5\right) \Rightarrow \left(\forall o \in M,\; \exists u \in M \to \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{Injective}\left(u\right) \land \left(u\left(o\right) = 1 \land \left(\operatorname{DenseRange}\left(u\right) \land \left(\left(\forall x \in M, y \in M, z \in M,\; u\left(\operatorname{tri}\left(C, x, y, z\right)\right) = \operatorname{tri}\left(\operatorname{quaternionModel}, u\left(x\right), u\left(y\right), u\left(z\right)\right)\right) \land \left(\forall x \in M, y \in M,\; \operatorname{kappa}\left(C, x, y\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, u\left(x\right), u\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.exists_unitQuaternion_embedding_denseRange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a ternary comparison structure on M whose transfer is order sensitive, whose reading is chain connected and takes values arbitrarily close to zero, and which has feature rank five: HasFeatureRank(C, 5) asserts that there is a map from M into Euclidean five-space whose inner products are the readings of C, that is, a realization of the reading in five dimensions. Completeness of the reading is not assumed. Then for every point o of M there is an injective map u from M into the unit quaternions with u(o) = 1 and dense range, which carries the transfer of C to the transfer p * q^-1 * r of the quaternion comparison model and preserves the reading, kappa(C, x, y) = (1 + <u(x), u(y)>) / 2. The argument: the normalized embedding of such a structure gives an injective map u with u(o) = 1, u(tri(C, x, y, z)) = u(x) * u(y)^-1 * u(z) and preserved reading. Its image contains 1 and is closed under products and inverses, since u(x) * u(y) = u(tri(C, x, o, y)) and u(x)^-1 = u(tri(C, o, x, o)); multiplication and inversion are continuous, so the closure K of the image is a closed subgroup of the unit quaternions. Between unit quaternions the reading is 1 - |p - q|^2 / 4, so two unit quaternions at distance less than min(1, e) have reading above 1 - e. For every e > 0, two points of the image are joined by a chain in the image whose consecutive readings exceed 1 - e, namely the image of such a chain in M. Two points of K have points of the image within distance min(1, e), so every two points of K are joined by a chain in K whose consecutive readings exceed 1 - e. Two points of M that do not commute in the group of C at o, whose product is tri(C, x, o, y), are carried to unit quaternions that do not commute, and both lie in K. A closed, noncommutative subgroup of the unit quaternions in which any two elements are joined by such chains for every e > 0 is the whole group, by eq_top_of_isClosed_of_chainConnected in `D5/B/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup`; so K is the whole group and the image of u is dense. When the reading of C is moreover complete, the image is also closed, hence the whole group, and u is a bijection; this is the identification of complete structures with the unit quaternions, which is not among the formal statements of the module. Without completeness u need not be onto: the countable dense subgroup constructed below has an induced structure satisfying all four hypotheses, and no map from a countable set onto the uncountable set of unit quaternions exists; this consequence is not among the formal statements of the module.

**Theorem 1.3 (On a subgroup, completeness of the reading is closedness).**

$$\forall H \in \operatorname{Subgroup}\left(\operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)\right),\; \operatorname{ReadingComplete}\left(\operatorname{subgroupModel}\left(H\right)\right) \Leftrightarrow \operatorname{IsClosed}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.subgroupModel_readingComplete_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a subgroup H of the unit quaternions, the reading of subgroupModel(H) is complete exactly when H is a closed subset of the unit quaternions. If the reading is complete, the inclusion of H into the unit quaternions preserves the reading, and the image of a reading-preserving map from a structure with complete reading into the unit quaternions is closed; this image is H. Conversely, let H be closed. The unit quaternions form a closed subset of the complete space of quaternions, so they are complete, and H, closed in them, is complete. Since the reading is 1 - |p - q|^2 / 4, a sequence x in H whose readings kappa(x(m), x(n)) exceed 1 - e^2 / 4 for all m and n beyond some N satisfies |x(m) - x(n)| < e there; so a sequence whose readings tend to one uniformly is a Cauchy sequence and converges to some a in H. For all n beyond some N the distance |x(n) - a| is less than min(1, e), and then the reading kappa(x(n), a) exceeds 1 - e, which is completeness of the reading. The statement is the classical fact that a subset of a complete metric space is complete exactly when it is closed, read through the reading.

**Theorem 1.4 (A dense subgroup satisfies every hypothesis except completeness).**

$$\forall H \in \operatorname{Subgroup}\left(\operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)\right),\; \operatorname{Dense}\left(H\right) \Rightarrow \left(\operatorname{Noncommutative}\left(\operatorname{subgroupModel}\left(H\right)\right) \land \left(\operatorname{ChainConnected}\left(\operatorname{subgroupModel}\left(H\right)\right) \land \left(\operatorname{TouchesZero}\left(\operatorname{subgroupModel}\left(H\right)\right) \land \operatorname{HasFeatureRank}\left(\operatorname{subgroupModel}\left(H\right), 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.subgroupModel_of_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a dense subgroup of the unit quaternions. Then subgroupModel(H) is noncommutative, chain connected, its reading touches zero, and it has feature rank five. Order sensitivity: the pairs (p, q) of unit quaternions with p * q different from q * p form an open set, which is nonempty because i * j = k and j * i = -k. The pairs of elements of H are dense among all pairs, so H contains such a pair p, q, and tri(p, 1, q) = p * q differs from tri(q, 1, p) = q * p. Readings near zero: the reading is continuous, so for e > 0 the pairs (p, q) with kappa(p, q) < e form an open set, nonempty because the reading of 1 and -1 is 0; it contains a pair of elements of H. Chains: the unit quaternions are the unit three-sphere in a real space of dimension four, which is connected. Fix d > 0 and let P(a, b) say that any element of H within distance d / 3 of a and any element of H within distance d / 3 of b are joined by a chain of elements of H whose consecutive distances are less than d. By the triangle inequality P(a, b) holds whenever |a - b| < d / 3, and P is transitive, because H has an element within distance d / 3 of the middle point at which two chains can be joined. On a connected space a transitive relation that holds between each point and all points of a neighbourhood holds between all pairs of points, so any two elements of H are joined by chains with steps of distance less than d. Taking d = min(1, e), consecutive readings along such a chain exceed 1 - e. Feature rank five: the feature map of the unit quaternions, which sends q to (1 / sqrt 2) * (1, re q, imI q, imJ q, imK q) in Euclidean five-space, restricted to H realizes the reading of subgroupModel(H) in five dimensions. A noncommutative, chain-connected ternary comparison structure whose reading is realized in Euclidean r-space has 5 <= r, by five_le_of_hasFeatureRank in `D5/B/S3/Quantum/AURICOmega/TernaryComparisonRankFive`; so five is the least such dimension for subgroupModel(H), and this combination is not among the formal statements of the module. Density cannot be omitted: the trivial subgroup is closed and its structure has a single point, so its transfer is not order sensitive; this consequence is not among the formal statements of the module.

**Theorem 1.5 (Completeness does not follow from the other hypotheses).**

$$\exists H \in \operatorname{Subgroup}\left(\operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)\right),\; \operatorname{Noncommutative}\left(\operatorname{subgroupModel}\left(H\right)\right) \land \left(\operatorname{ChainConnected}\left(\operatorname{subgroupModel}\left(H\right)\right) \land \left(\operatorname{TouchesZero}\left(\operatorname{subgroupModel}\left(H\right)\right) \land \left(\operatorname{HasFeatureRank}\left(\operatorname{subgroupModel}\left(H\right), 5\right) \land \left(\neg \operatorname{ReadingComplete}\left(\operatorname{subgroupModel}\left(H\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.exists_subgroupModel_not_readingComplete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a subgroup H of the unit quaternions such that subgroupModel(H) is noncommutative, chain connected, its reading touches zero and it has feature rank five, while its reading is not complete. Hence completeness of the reading is not implied by the other four hypotheses under which a complete structure is identified with the unit quaternions. The unit quaternions form a separable metric space, so they have a countable dense subset S, and the subgroup H generated by S, the image of the free group on S, is countable and dense. The unit quaternions are uncountable: for every t in [-1, 1] the quaternion with real part t, i-coordinate sqrt(1 - t^2) and the other coordinates 0 has norm one, so the real parts of unit quaternions fill the uncountable interval [-1, 1]. By the previous theorem subgroupModel(H) has the four properties. If its reading were complete, H would be closed by the characterization of completeness on subgroups, so H would equal its closure, which is the whole group of unit quaternions since H is dense, contradicting the countability of H.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.exists_subgroupModel_not_readingComplete`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.exists_unitQuaternion_embedding_denseRange`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.subgroupModel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.subgroupModel_of_dense`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonCompletion.subgroupModel_readingComplete_iff`
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism](TernaryComparisonIsomorphism.md)
