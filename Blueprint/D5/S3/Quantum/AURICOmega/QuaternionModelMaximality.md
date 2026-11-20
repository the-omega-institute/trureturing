# Maximality of the unit quaternion comparison model in small feature rank

## Abstract

A ternary comparison structure of feature rank at most eight that contains a transfer- and reading-preserving copy of the unit quaternion comparison model is that copy, eight is the largest rank with this property, and in feature rank five a reading-preserving copy alone already exhausts the structure.

**Theorem 1.1 (A transfer- and reading-preserving copy of the model in feature rank at most eight is everything).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall r \in \mathbb{N},\; \operatorname{HasFeatureRank}\left(C, r\right) \Rightarrow \left(r \le 8 \Rightarrow \left(\forall j \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to M,\; \left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), z \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; j\left(\operatorname{tri}\left(\operatorname{quaternionModel}, x, y, z\right)\right) = \operatorname{tri}\left(C, j\left(x\right), j\left(y\right), j\left(z\right)\right)\right) \Rightarrow \left(\left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{kappa}\left(C, j\left(x\right), j\left(y\right)\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y\right)\right) \Rightarrow \operatorname{Bijective}\left(j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionModelMaximality.bijective_of_hasFeatureRank_le_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a ternary comparison structure on M whose reading is the Gram kernel of a map into Euclidean r-space with r <= 8, and let j be a map from the unit quaternions into M that carries the transfer x * y^-1 * z of the model to the transfer of C and preserves the reading. Then j is a bijection. A preserved reading makes j injective, since reading one characterizes equality. For a point m of M, the readings kappa(C, j(y), m) form a one-point extension of the quaternion reading with self-reading one, so by the classification of one-point extensions they are (a + <b, y>) / sqrt 2 with a^2 + |b|^2 <= 1. Transfer preservation and the invariance laws of the reading show that the right translate x -> tri(C, m, j(1), j(x)) of the copy reads (a + <b * x, y>) / sqrt 2 against j(y). For e = 1, i, j and k, the differences of the features of the translate at e and at -e have the components orthogonal to all features of the copy pairwise orthogonal, with squared norm 2 - 4 * |b|^2. Together with the five orthogonal vectors formed from the features of the copy at 1 and -1 and at e and -e, they would be nine nonzero orthogonal vectors if |b|^2 < 1 / 2, which is impossible in dimension at most eight. Hence |b|^2 = 1 / 2; nonnegativity of the readings gives a = |b| = 1 / sqrt 2, and m has reading one with the image of the unit quaternion sqrt 2 * b, so m lies in the image of j. Neither noncommutativity, chain connectivity, touching zero nor completeness of the reading of C is assumed. Reading preservation cannot be dropped: a constant map preserves the transfer and is not injective. Whether transfer preservation can be dropped in feature rank six, seven or eight is not settled here; in feature rank five it can, as the last theorem shows.

**Theorem 1.2 (Eight is the sharp rank).**

$$\forall r \in \mathbb{N},\; \left(\forall M \in \operatorname{Type},\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall j \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to M,\; \operatorname{HasFeatureRank}\left(C, r\right) \Rightarrow \left(\left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), z \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; j\left(\operatorname{tri}\left(\operatorname{quaternionModel}, x, y, z\right)\right) = \operatorname{tri}\left(C, j\left(x\right), j\left(y\right), j\left(z\right)\right)\right) \Rightarrow \left(\left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{kappa}\left(C, j\left(x\right), j\left(y\right)\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y\right)\right) \Rightarrow \operatorname{Bijective}\left(j\right)\right)\right)\right) \Leftrightarrow r \le 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionModelMaximality.forall_bijective_iff_le_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural number r, every transfer- and reading-preserving copy of the unit quaternion comparison model inside a ternary comparison structure of feature rank r is a bijection exactly when r <= 8. For r <= 8 this is the previous theorem. For r >= 9, take two copies of the unit quaternions, M = unitary(H) x Bool, with transfer (x * y^-1 * z, a xor b xor c) and with the reading of the model within a layer and the reading one half between the layers. Its reading is the Gram kernel of the map into Euclidean nine-space sending (x, false) to (1, x, 0) / sqrt 2 and (x, true) to (1, 0, x) / sqrt 2, where x stands for the four quaternion coordinates and 0 for four zeros; so the structure has feature rank nine and hence every larger rank. The layer x -> (x, false) preserves transfer and reading and misses the second layer.

**Theorem 1.3 (In feature rank five a reading-preserving copy is everything).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \operatorname{HasFeatureRank}\left(C, 5\right) \Rightarrow \left(\forall j \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to M,\; \left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{kappa}\left(C, j\left(x\right), j\left(y\right)\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y\right)\right) \Rightarrow \operatorname{Bijective}\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionModelMaximality.bijective_of_hasFeatureRank_five_of_kappa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a ternary comparison structure on M of feature rank five and let j be a map from the unit quaternions into M that preserves the reading. Then j is a bijection; the transfer need not be preserved. For a point m, the translate x -> tri(C, m, j(1), j(x)) is again a reading-preserving copy and sends 1 to m. Each translate point reads (a + <b, y>) / sqrt 2 against j(y) with a^2 + |b|^2 = 1, by the classification of one-point extensions of feature rank five, and |b| <= a because the readings are nonnegative; so its readings against j(1) and j(-1) add up to sqrt 2 * a >= 1. These sums, as functions of x, form a one-point extension of feature rank five of the translated copy by the unit vector (phi(j(1)) + phi(j(-1))) / sqrt 2, where phi is the feature map of C; hence the sums at x and at -x add up to at most two, and the sum at x = 1, which belongs to m, equals one. For the readings of m this means 2 * a = sqrt 2 and |b|^2 = 1 / 2, so m has reading one with the image of the unit quaternion sqrt 2 * b and lies in the image of j.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionModelMaximality.bijective_of_hasFeatureRank_five_of_kappa`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionModelMaximality.bijective_of_hasFeatureRank_le_eight`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionModelMaximality.forall_bijective_iff_le_eight`
- Dependency: [D5/S3/Quantum/AURICOmega/GramRankFeatureMap](GramRankFeatureMap.md)
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension](QuaternionReadingOnePointExtension.md)
