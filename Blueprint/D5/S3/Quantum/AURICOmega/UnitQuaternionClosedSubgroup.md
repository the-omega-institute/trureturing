# Closed chain-connected subgroups of the unit quaternions

## Abstract

A closed, noncommutative subgroup of the unit quaternions in which any two elements are joined, for every positive tolerance, by a chain of elements of the subgroup with consecutive readings of the quaternion comparison model within that tolerance of one, is the whole group.

**Lemma 1.1 (A quaternion of squared norm one is a unit quaternion).**

$$\forall u \in \mathbb{H}[\mathbb{R}],\; \operatorname{normSq}\left(u\right) = 1 \Rightarrow u \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup.mem_unitary_of_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here normSq(u) is the squared norm u * star u, the sum of the squares of the four components of u, regarded as a real number. Both star u * u and u * star u equal normSq(u), which is 1, so u is a unitary element of the real quaternion algebra.

**Lemma 1.2 (The components of a unit quaternion have squares summing to one).**

$$\forall u \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{re}\left(u\right)^{2} + \operatorname{imI}\left(u\right)^{2} + \operatorname{imJ}\left(u\right)^{2} + \operatorname{imK}\left(u\right)^{2} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup.sq_add_sq_coe_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit quaternion u has norm one, so its squared norm u * star u is 1; and the squared norm of a quaternion is the sum of the squares of its real part and its three imaginary components re, imI, imJ and imK.

**Theorem 1.3 (A closed, chain-connected, noncommutative subgroup is the whole group).**

$$\forall H \in \operatorname{Subgroup}\left(\operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)\right),\; \operatorname{IsClosed}\left(H\right) \Rightarrow \left(\left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\forall x \in H, y \in H,\; \operatorname{ReflTransGen}\left(\lambda a b. b \in H \land 1 - e < \operatorname{kappa}\left(\operatorname{quaternionModel}, a, b\right), x, y\right)\right)\right) \Rightarrow \left(\left(\exists x \in H, y \in H,\; x \cdot y \ne y \cdot x\right) \Rightarrow H = \operatorname{top}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup.eq_top_of_isClosed_of_chainConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here unitary(H[R]) is the group of unit quaternions, IsClosed(H) says that H is closed as a subset of it, top is the whole group, and kappa(quaternionModel, a, b) = (1 + <a, b>) / 2 is the reading of the quaternion comparison model, with <a, b> the real inner product of quaternions. The second hypothesis says that for every e > 0 any two elements of H are joined by a finite chain of elements of H whose consecutive readings exceed 1 - e. Without the noncommutativity hypothesis the conclusion fails, because the trivial subgroup is closed, as a one-element subset, and satisfies the chain condition, as every chain in it is trivial; this consequence is not among the formal statements of the module. The statement is classical: a closed subgroup is compact, the reading is 1 - |x - y|^2 / 4, so the chain condition says that any two elements are joined inside H by chains with arbitrarily small steps, and for a compact metric space this is equivalent to connectedness; hence the statement is the fact that a closed connected nonabelian subgroup of the unit quaternions, the group SU(2), is the whole group, and the argument below is elementary and uses no Lie theory; this equivalence and this classical fact are not among the formal statements of the module. Small elements. Since H contains two elements that do not commute, it contains an element other than 1, and for every e > 0 a chain in H from 1 to that element has a step from 1 to an element b of H different from 1 with kappa(1, b) > 1 - e. As kappa(1, b) = (1 + re b) / 2, the subgroup H contains elements h_k different from 1 whose real parts tend to 1. A limiting axis and a full circle. Write h_k = cos t_k + sin t_k * n_k with t_k = arccos(re h_k) and n_k a unit imaginary quaternion; the angles t_k are positive and tend to 0. By compactness of the unit sphere of imaginary quaternions a subsequence of the n_k converges to a unit imaginary quaternion a. For t >= 0, de Moivre's formula writes the power of h_k with exponent m_k, the integer part of t / t_k, as cos(m_k t_k) + sin(m_k t_k) * n_k, and m_k t_k tends to t, so along the subsequence these powers converge to cos t + sin t * a. As H is closed, it contains cos t + sin t * a for every t >= 0, and, taking inverses, for every real t. Call a unit imaginary quaternion with this property an axis of H. A second axis. Let n be the axis just found. The unit imaginary quaternions n and i have the same reading against 1, so by two-point homogeneity some unit quaternion p satisfies p * n * p^-1 = i, and conjugation by p serves as coordinates in which n is i. Quaternions commuting with i are those with vanishing j and k coordinates, so quaternions commuting with n commute with each other, and since H is noncommutative some element of H does not commute with n. Along a chain in H from 1 to that element with consecutive readings above 1/2 there are consecutive elements c and d with c commuting with n and d not; then g = c^-1 * d lies in H, does not commute with n, and kappa(1, g) = kappa(c, d) > 1/2; the conjugate p * g * p^-1 has the same reading against 1, so it has positive real part, and it does not commute with i. Conjugating an axis by an element of H gives an axis, so g * n * g^-1 is an axis; its image under conjugation by p is the conjugate of i by p * g * p^-1, and because p * g * p^-1 has positive real part and does not commute with i, the i coordinate of that image has square less than 1, so this axis is neither n nor -n. All axes, by rotating axes about one another. The negative of an axis is an axis, and conjugating an axis b by cos s + sin s * a, with a an axis, gives an axis. In the coordinates where n is i, conjugating i by cos s + sin s * a, where a has i coordinate h with h^2 < 1, reaches every i coordinate in the interval from 2 h^2 - 1 to 1. Starting from the second axis, taken with nonnegative i coordinate h0 < 1, each such step either reaches the i coordinate 0 or lowers the i coordinate by at least 1 - h0 while keeping it nonnegative, so after finitely many steps some axis has i coordinate 0. Conjugating i by cos s + sin s * a, with a that axis, gives axes of every i coordinate between -1 and 1, and conjugation by cos s + sin s * i moves an axis along its circle of constant i coordinate to every point of that circle, so every unit imaginary quaternion is an axis of H. Polar form. Every unit quaternion u equals cos t + sin t * m with t = arccos(re u) and m a unit imaginary quaternion; since m is an axis of H, u lies in H, and H is the whole group.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup.eq_top_of_isClosed_of_chainConnected`
- Truth anchor: `D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup.mem_unitary_of_normSq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup.sq_add_sq_coe_unitary`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity](QuaternionTwoPointHomogeneity.md)
- Dependency: [D5/S3/Quantum/AURICOmega/UnitQuaternionPolar](UnitQuaternionPolar.md)
