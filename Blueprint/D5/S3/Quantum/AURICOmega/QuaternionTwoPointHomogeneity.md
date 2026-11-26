# Two-point homogeneity of the quaternion comparison model

## Abstract

Left-right translations by unit quaternions preserve the reading of the quaternion comparison model and act transitively on pairs with equal reading.

**Lemma 1.1 (The reading is invariant under left-right translation).**

$$\forall p \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), q \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{kappa}\left(\operatorname{quaternionModel}, p \cdot x \cdot q, p \cdot y \cdot q\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity.kappa_mul_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the quaternion comparison model the transfer is tri a b c = a * b^-1 * c, so with the unit quaternion 1 as middle argument the products p * x and x * q are the transfers tri p 1 x and tri x 1 q. The reading is invariant under a transfer on the left and under a transfer on the right, so it is unchanged when both arguments are first multiplied by p on the left and then by q on the right. Equivalently, z -> p * z * q is a linear isometry of the quaternions, and the reading (1 + <x, y>) / 2 depends only on the real inner product.

**Lemma 1.2 (Unit quaternions with equal real part are conjugate).**

$$\forall a \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), b \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{re}\left(a\right) = \operatorname{re}\left(b\right) \Rightarrow \left(\exists c \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; c \cdot a = b \cdot c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity.exists_unitary_mul_eq_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second unit quaternion, written a' in the source, is written b in the formula. Two unit quaternions a and b have the same norm one, so when they also have the same real part their imaginary parts have the same length. A nonzero quaternion w with w * a = b * w then exists: with imaginary parts u of a and v of b, the quaternion |u|^2 - v * u works unless v = -u, and otherwise any nonzero imaginary quaternion orthogonal to u works. Dividing w by its norm gives a unit quaternion c with c * a = b * c.

**Theorem 1.3 (Pairs with equal reading are related by a left-right translation).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), u \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), v \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, u, v\right) \Rightarrow \left(\exists p \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), q \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; p \cdot x \cdot q = u \land p \cdot y \cdot q = v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity.exists_mul_mul_eq_of_kappa_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second pair is written u and v in the formula. By the invariance above with p = x^-1 and q = 1, the reading of x and y equals the reading of 1 and x^-1 * y, which is (1 + re (x^-1 * y)) / 2. Equal readings therefore give the unit quaternions a = x^-1 * y and a' = u^-1 * v the same real part; they also have the same norm one. By the conjugacy of unit quaternions with equal real part, there is a unit quaternion c with c * a = a' * c. The translation with p = u * c * x^-1 and q = c^-1 then sends x to u, and it sends y to u * c * a * c^-1 = u * a' = v.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity.exists_mul_mul_eq_of_kappa_eq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity.exists_unitary_mul_eq_mul`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity.kappa_mul_mul`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
