# The unit quaternion comparison model

## Abstract

The unit quaternions with the half-shifted inner product form a ternary comparison structure that is order sensitive, touches zero, is chain connected and has feature rank five.

**Lemma 1.1 (The quaternion inner product in components).**

$$\forall p \in \mathbb{H}[\mathbb{R}], q \in \mathbb{H}[\mathbb{R}],\; \langle p, q \rangle_{\mathbb{R}} = \operatorname{re}\left(p\right) \cdot \operatorname{re}\left(q\right) + \operatorname{imI}\left(p\right) \cdot \operatorname{imI}\left(q\right) + \operatorname{imJ}\left(p\right) \cdot \operatorname{imJ}\left(q\right) + \operatorname{imK}\left(p\right) \cdot \operatorname{imK}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.inner_eq_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real inner product of two quaternions is the real part of star p * q. Since star p has components re p, -imI p, -imJ p and -imK p, that real part is the sum of the four products of corresponding components.

**Definition 1.2 (The unit quaternions as a ternary comparison structure).**

Lean statement: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel`

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the group of unit quaternions, the unitary elements of the real quaternion algebra. The transfer is tri x y z = x * y^-1 * z and the reading is kappa x y = (1 + <x, y>) / 2, where <p, q> = re p * re q + imI p * imI q + imJ p * imJ q + imK p * imK q is the real inner product of the quaternion algebra. The transfer identities are group identities. The reading is symmetric; it equals one exactly when x = y, because two unit vectors have inner product one only when they coincide; it is nonnegative because the inner product of two unit vectors is at least -1. Left and right multiplication by a unit quaternion preserve the inner product, which gives the two invariance laws of the reading under transfer. The Gram forms are nonnegative because the reading is the inner product of the feature vectors described below, so each Gram form is the squared norm of a combination of feature vectors.

**Definition 1.3 (The unit quaternion i).**

Lean statement: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.unitI`

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.unitI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

unitI is the quaternion with real part 0 and imaginary components imI = 1, imJ = 0, imK = 0, regarded as a unit quaternion: star i * i = 1 and i * star i = 1.

**Theorem 1.4 (The model is order sensitive).**

$$\operatorname{Noncommutative}\left(\operatorname{quaternionModel}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_noncommutative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the unit quaternions i, 1 and j. Then tri i 1 j = i * j = k while tri j 1 i = j * i = -k; their k-components are 1 and -1, so the two transfers differ.

**Theorem 1.5 (The reading touches zero).**

$$\operatorname{TouchesZero}\left(\operatorname{quaternionModel}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_touchesZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antipodal pair 1 and -1 has <1, -1> = -1, so its reading is (1 - 1) / 2 = 0, which is below every positive real e.

**Theorem 1.6 (The model is chain connected).**

$$\operatorname{ChainConnected}\left(\operatorname{quaternionModel}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_chainConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit quaternions are exactly the quaternions of norm one, the unit three-sphere in a real space of dimension four, and this sphere is connected. For a fixed point a the reading kappa a b is continuous in b and equals one at b = a, so for positive e every b near a satisfies 1 - e < kappa a b and, by symmetry, 1 - e < kappa b a. Thus, for each point a, the relation holds in both directions, from a to b and from b to a, for every b in a neighbourhood of a. On a connected space, a transitive relation with this two-sided neighbourhood property holds between all pairs; applied to the reflexive transitive closure of 1 - e < kappa a b, this joins any two unit quaternions.

**Theorem 1.7 (The reading has feature rank five).**

$$\operatorname{HasFeatureRank}\left(\operatorname{quaternionModel}, 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_hasFeatureRank_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The feature map sends q to (1 / sqrt 2) * (1, re q, imI q, imJ q, imK q) in Euclidean five-space. The inner product of the features of p and q is (1 / 2) * (1 + <p, q>), which is the reading of p and q.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.inner_eq_components`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_chainConnected`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_hasFeatureRank_five`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_noncommutative`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.quaternionModel_touchesZero`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.unitI`
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonGroup](TernaryComparisonGroup.md)
