# The phase circle of the unit quaternions and the fibre extremum of the reading

## Abstract

Along a right coset of the phase circle of the unit quaternions the round-trip reading and the squared shifted reading attain the ray kernel as their maximum, and the squared inner product has the ray kernel times pi as its integral over a full turn.

**Definition 1.1 (The phase circle).**

$$\forall c \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; c \in \operatorname{phaseCircle} \Leftrightarrow \left(\operatorname{imJ}\left(c\right) = 0 \land \operatorname{imK}\left(c\right) = 0\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.phaseCircle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

phaseCircle is the subgroup of the unit quaternions whose elements have vanishing j and k components, that is the unit quaternions a + b i with a^2 + b^2 = 1. It is closed under products because the j and k components of a product of two elements of the real span of 1 and i vanish, and under inverses because the inverse of a unit quaternion is its conjugate. The quotient of the unit quaternions by this subgroup is formed with the cosets x * phaseCircle, so two unit quaternions lie in the same class exactly when they differ by a factor of the circle on the right. Remark (not stated as a theorem here): the Hopf map sends x to x * i * star x, and the ray kernel is a function of the inner product of Hopf images, equal to one exactly on the right cosets of the phase circle; together with the conjugacy of unit quaternions with equal real parts, these results show that the Hopf map identifies the quotient of the unit quaternions by the phase circle with the sphere of unit imaginary quaternions.

**Theorem 1.2 (Maximum and integral of the reading over a fibre).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{IsGreatest}\left(\{r \mid \exists c \in \operatorname{phaseCircle},\; r = \operatorname{kappa}\left(\operatorname{quaternionModel}, y, \operatorname{tri}\left(\operatorname{quaternionModel}, x \cdot c, y, x \cdot c\right)\right)\}, \operatorname{rayKernel}\left(x, y\right)\right) \land \left(\operatorname{IsGreatest}\left(\{r \mid \exists c \in \operatorname{phaseCircle},\; r = \left(2 \cdot \operatorname{kappa}\left(\operatorname{quaternionModel}, x \cdot c, y\right) - 1\right)^{2}\}, \operatorname{rayKernel}\left(x, y\right)\right) \land \int_{0}^{2\pi} \left(\langle x \cdot \operatorname{mk}\left(\operatorname{cos}\left(t\right), \operatorname{sin}\left(t\right), 0, 0\right), y \rangle_{\mathbb{R}}\right)^{2} dt = \pi \cdot \operatorname{rayKernel}\left(x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.rayKernel_isGreatest_and_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display, kappa and tri are the reading and the transfer of the quaternion comparison model, with kappa(x, y) = (1 + <x, y>) / 2 and tri(p, y, p) = p * y^-1 * p, IsGreatest(S, m) means that m belongs to S and bounds S from above, mk(a, b, c, d) is the quaternion a + b i + c j + d k, and the integration variable t runs over the interval from 0 to 2 pi. For all unit quaternions x and y the three conjuncts state: over the right phase circle of x, the round-trip reading kappa(y, (x c) y^-1 (x c)) has largest value rayKernel(x, y); the squared shifted reading (2 kappa(x c, y) - 1)^2 has the same largest value; and the integral over a full turn of the squared inner product of x (cos t + sin t i) with y equals pi times rayKernel(x, y). Put A = 2 kappa(x, y) - 1 and B = 2 kappa(x, y * i) - 1, so that rayKernel(x, y) = A^2 + B^2 by definition. For a phase c = a + b i one has 2 kappa(x c, y) - 1 = a A - b B, since right multiplication by a + b i mixes the inner products with y and with y * i. Over the circle a^2 + b^2 = 1 the square (a A - b B)^2 is at most A^2 + B^2 by the Cauchy-Schwarz inequality, with equality at a = A / r, b = -B / r for r the square root of A^2 + B^2, and at c = 1 when A = B = 0. For a unit quaternion p the round-trip identity kappa(y, p y^-1 p) = (2 kappa(p, y) - 1)^2 holds, because the real part of y^-1 p y^-1 p equals 2 <p, y>^2 - 1 for unit p and y; so the first set equals the second. Finally the squared inner product along the circle is A^2 cos^2 t + B^2 sin^2 t - 2 A B sin t cos t, whose integral over a full turn is pi (A^2 + B^2). Thus the ray kernel is both the fibre maximum of the round-trip reading and pi^-1 times the integral of the squared inner product over the fibre, that is twice its mean over a full turn.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.phaseCircle`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.rayKernel_isGreatest_and_integral`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionRayKernel](QuaternionRayKernel.md)
- Dependency: [D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup](UnitQuaternionClosedSubgroup.md)
