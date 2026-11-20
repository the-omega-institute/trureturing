# The unit quaternions modulo sign as a ternary comparison structure

## Abstract

The unit quaternions modulo sign, with transfer x * y^-1 * z and reading <x, y>^2, form a noncommutative, chain-connected, reading-complete ternary comparison structure touching zero whose reading has feature rank ten but not nine, and in which every point has two distinct points of reading zero.

**Definition 1.1 (The sign subgroup).**

Lean statement: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.signSubgroup`

*Formalization.* `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.signSubgroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

signSubgroup is the subgroup of the group of unit quaternions whose elements are exactly 1 and -1. It contains 1, and it is closed under products and inverses because (-1) * (-1) = 1 and (-1)^-1 = -1.

**Definition 1.2 (The sign subgroup is normal).**

$$\operatorname{Normal}\left(\operatorname{signSubgroup}\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.signSubgroup_normal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subgroup signSubgroup is normal: for g a unit quaternion, g * 1 * g^-1 = 1 and g * (-1) * g^-1 = -1, since -1 is central in the quaternions.

**Definition 1.3 (Unit quaternions modulo sign).**

Lean statement: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.ProjectiveQuaternion`

*Formalization.* `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.ProjectiveQuaternion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ProjectiveQuaternion is the quotient group of the unit quaternions by the normal subgroup signSubgroup. Two unit quaternions x and y have the same class exactly when x^-1 * y is 1 or -1, that is, when y = x or y = -x. Classically, the unit quaternions modulo sign are the rotation group of Euclidean three-space, through the action q acting by v mapsto q * v * q^-1 on the imaginary quaternions; this identification is a remark only and is not part of the definition.

**Definition 1.4 (The structure on unit quaternions modulo sign).**

Lean statement: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.projectiveModel`

*Formalization.* `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.projectiveModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

projectiveModel is the ternary comparison structure on ProjectiveQuaternion whose transfer is tri x y z = x * y^-1 * z, computed in the quotient group, and whose reading kappa of the classes of unit quaternions x and y is <x, y>^2, where <x, y> = re x * re y + imI x * imI y + imJ x * imJ y + imK x * imK y is the real inner product of the quaternions. The reading is well defined because changing the sign of either representative changes the sign of <x, y> and leaves its square unchanged. The transfer identities are group identities. The reading is symmetric and nonnegative. It equals one exactly when the two classes agree: two unit vectors satisfy <x, y>^2 = 1 only when <x, y> = 1 or <x, y> = -1, that is, when y = x or y = -x. Multiplication on the right by u^-1 * v and on the left by u * v^-1 preserves the inner product of unit quaternions, which gives the two invariance laws of the reading under transfer. The Gram forms are nonnegative because the reading is the inner product of the feature vectors described with the theorem below, so each Gram form is the squared norm of a combination of feature vectors.

**Theorem 1.5 (Feature rank ten and the remaining properties).**

$$\operatorname{Noncommutative}\left(\operatorname{projectiveModel}\right) \land \left(\operatorname{ChainConnected}\left(\operatorname{projectiveModel}\right) \land \left(\operatorname{TouchesZero}\left(\operatorname{projectiveModel}\right) \land \left(\operatorname{ReadingComplete}\left(\operatorname{projectiveModel}\right) \land \left(\operatorname{HasFeatureRank}\left(\operatorname{projectiveModel}, 10\right) \land \left(\left(\neg \operatorname{HasFeatureRank}\left(\operatorname{projectiveModel}, 9\right)\right) \land \left(\forall p \in \operatorname{ProjectiveQuaternion},\; \exists a \in \operatorname{ProjectiveQuaternion}, b \in \operatorname{ProjectiveQuaternion},\; a \ne b \land \left(\operatorname{kappa}\left(\operatorname{projectiveModel}, p, a\right) = 0 \land \operatorname{kappa}\left(\operatorname{projectiveModel}, p, b\right) = 0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.projectiveModel_featureRank_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Noncommutativity: take the classes of i, 1 and r = (3 + 4 j) / 5. Then tri i 1 r = i * r and tri r 1 i = r * i, and the unit quaternions i * r and r * i have inner product -7 / 25, which is neither 1 nor -1, so their classes differ. Chain connectedness: the unit-quaternion structure with reading (1 + <a, b>) / 2 is chain connected. A step with 1 - e / 4 < (1 + <a, b>) / 2 gives 1 - e / 2 < <a, b>, and since t^2 >= 2 t - 1 for every real t, it gives 1 - e < <a, b>^2; so a chain of unit quaternions for e / 4 maps to a chain of classes for e. Touching zero: the classes of 1 and i have reading <1, i>^2 = 0. Reading completeness: for a sequence of classes whose readings with each other tend to one, choose representatives on the unit sphere of the quaternions. The sphere is compact, so a subsequence of representatives converges to a unit quaternion a; for each fixed n the readings of the n-th class with the subsequence converge to the reading of the n-th class with the class of a, so the readings of the sequence with the class of a tend to one. Feature rank ten: the map q mapsto (re q^2, imI q^2, imJ q^2, imK q^2, sqrt 2 * q_a * q_b for the six pairs a < b) into Euclidean ten-space, applied to a representative, satisfies <f(p), f(q)> = <p, q>^2, because the square of a sum of four products expands into the four squared products and twice the six cross products. No feature rank nine: suppose the reading is the Gram kernel of a map g into Euclidean nine-space. Take the ten unit quaternions t_1, ..., t_10 given by 1, i, j, k and (3 e_a + 4 e_b) / 5 for the six pairs a < b of the basis e_1, ..., e_4 = 1, i, j, k. If the combination sum_a c_a g(t_a) vanishes, its inner products with the vectors g(t_b) give the ten linear equations sum_a c_a <t_a, t_b>^2 = 0 in the ten unknowns c_a, and solving this system explicitly gives c = 0. Conceptually, the only quadratic form vanishing at all ten points is zero: a form vanishing at 1, i, j and k has zero diagonal coefficients, and its value at (3 e_a + 4 e_b) / 5 is then 12 / 25 times its coefficient of y_a y_b. Hence the ten squared linear forms <t_a, y>^2 form a basis of the ten-dimensional space of quadratic forms in y, and the matrix of the system is invertible. So the ten vectors g(t_a) are linearly independent, which is impossible in a space of dimension nine. Two points of reading zero: for every unit quaternion x, left multiplication by x preserves the inner product, so the readings of x with x * i and x * j are <1, i>^2 = 0 and <1, j>^2 = 0, and the classes of x * i and x * j differ because their reading is <i, j>^2 = 0 rather than one. Since a map into Euclidean five-space followed by the inclusion into nine-space would give feature rank nine, the reading does not have feature rank five either. Thus the structure is noncommutative, chain connected, touches zero and has complete reading, which are all the qualitative hypotheses under which a structure of feature rank five is isomorphic to the unit-quaternion structure; the comparison with that structure is separated by the minimal feature rank alone, ten here against five there. In the unit-quaternion structure the only point of reading zero with x is -x, while here every point has at least two distinct points of reading zero. The number ten is the dimension of the space of quadratic forms in four variables, the classical dimension of the symmetric square of a four-dimensional space; its decomposition as 1 + 9, the constants together with the matrix coefficients of the three-dimensional rotation representation, is also classical. The theorem is a statement about this one explicit structure; the count is not claimed as new.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.ProjectiveQuaternion`
- Truth anchor: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.projectiveModel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.projectiveModel_featureRank_ten`
- Truth anchor: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.signSubgroup`
- Truth anchor: `D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel.signSubgroup_normal`
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism](TernaryComparisonIsomorphism.md)
