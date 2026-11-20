# The Hopf fibration of the unit quaternions and the fibre extremum of the reading

## Abstract

The Hopf map sends the unit quaternions onto the unit imaginary quaternions and identifies their quotient by the phase circle with that two-sphere; along a phase circle the squared reading attains the ray kernel as its maximum and has the ray kernel times pi as its integral over a full turn.

**Definition 1.1 (The phase circle).**

$$\forall c \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; c \in \operatorname{phaseCircle} \Leftrightarrow \left(\operatorname{imJ}\left(c\right) = 0 \land \operatorname{imK}\left(c\right) = 0\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.phaseCircle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

phaseCircle is the subgroup of the unit quaternions whose elements have vanishing j and k components, that is the unit quaternions a + b i with a^2 + b^2 = 1. It is closed under products because the j and k components of a product of two elements of the real span of 1 and i vanish, and under inverses because the inverse of a unit quaternion is its conjugate. The quotient of the unit quaternions by this subgroup is formed with the cosets x * phaseCircle, so two unit quaternions lie in the same class exactly when they differ by a factor of the circle on the right.

**Theorem 1.2 (The range of the Hopf map).**

$$\operatorname{range}\left(\operatorname{hopf}\right) = \{n \in \mathbb{H}[\mathbb{R}] \mid \operatorname{re}\left(n\right) = 0 \land \left\lVert n \right\rVert = 1\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.range_hopf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Heinz Hopf (1931). *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*. DOI: [10.1007/BF01457962](https://doi.org/10.1007/BF01457962).

*Commentary.*

The Hopf map sends a unit quaternion x to hopf x = x * i * star x. The statement is that its range is exactly the set of quaternions n with real part re(n) = 0 and norm one. The image lies in this set because the norm is multiplicative and conjugation preserves the real part, which is zero for i. Conversely, let n be imaginary of norm one. If n is not -i, put q = 1 - n * i; a computation in components gives q * i * star q = |q|^2 n with |q|^2 = 2 (1 + n_i), where n_i is the i component of n, so this number is positive and the normalization q / |q| is a unit quaternion with Hopf image n. If n = -i, the unit quaternion j has Hopf image j * i * star j = -i. That the quadratic map of the three-sphere onto the two-sphere is surjective goes back to Hopf; the quaternion form of the map and the explicit preimages are derived here.

**Theorem 1.3 (The quotient by the phase circle is the two-sphere).**

$$\exists e \in \operatorname{Homeomorph}\left(\operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) / \operatorname{phaseCircle}, \{n \in \mathbb{H}[\mathbb{R}] \mid \operatorname{re}\left(n\right) = 0 \land \left\lVert n \right\rVert = 1\}\right),\; \forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; e\left(\operatorname{mk}\left(x\right)\right) = \operatorname{hopf}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.exists_homeomorph_quotient_phaseCircle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Heinz Hopf (1931). *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*. DOI: [10.1007/BF01457962](https://doi.org/10.1007/BF01457962).

*Commentary.*

In the display, the quotient is the space of cosets x * phaseCircle with the quotient topology, mk(x) is the class of x, Homeomorph(A, B) is the type of homeomorphisms from A onto B, and the sphere on the right carries the subspace topology of the unit imaginary quaternions; the value e(mk(x)) is read as a quaternion. The statement is that some homeomorphism e from the quotient onto the unit imaginary sphere sends the class of every unit quaternion x to its Hopf image. Two unit quaternions have the same Hopf image exactly when they differ by a right factor in the phase circle: equal Hopf images give ray kernel one, by the expression of the ray kernel through the inner product of the Hopf images, and the ray kernel equals one exactly on the right phase cosets; conversely, a right phase factor gives ray kernel one, and two unit vectors with inner product one coincide. Hence the Hopf map descends to a continuous injection on the quotient, which is onto by the range theorem. The unit quaternions form the compact three-sphere and the target is Hausdorff, so this continuous bijection from a compact space is a homeomorphism. The fibres of the Hopf map are the great circles of Hopf's fibration; the description as right cosets of the phase circle and the homeomorphism statement are derived here.

**Theorem 1.4 (Maximum and mean of the reading over a fibre).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{IsGreatest}\left(\{r \mid \exists c \in \operatorname{phaseCircle},\; r = \operatorname{kappa}\left(\operatorname{quaternionModel}, y, \operatorname{tri}\left(\operatorname{quaternionModel}, x \cdot c, y, x \cdot c\right)\right)\}, \operatorname{rayKernel}\left(x, y\right)\right) \land \left(\operatorname{IsGreatest}\left(\{r \mid \exists c \in \operatorname{phaseCircle},\; r = \left(2 \cdot \operatorname{kappa}\left(\operatorname{quaternionModel}, x \cdot c, y\right) - 1\right)^{2}\}, \operatorname{rayKernel}\left(x, y\right)\right) \land \int_{0}^{2\pi} \left(\langle x \cdot \operatorname{mk}\left(\operatorname{cos}\left(t\right), \operatorname{sin}\left(t\right), 0, 0\right), y \rangle_{\mathbb{R}}\right)^{2} dt = \pi \cdot \operatorname{rayKernel}\left(x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.rayKernel_isGreatest_and_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display, kappa and tri are the reading and the transfer of the quaternion comparison model, with kappa(x, y) = (1 + <x, y>) / 2 and tri(p, y, p) = p * y^-1 * p, IsGreatest(S, m) means that m belongs to S and bounds S from above, mk(a, b, c, d) is the quaternion a + b i + c j + d k, and the integration variable t runs over the interval from 0 to 2 pi. For all unit quaternions x and y the three conjuncts state: over the right phase circle of x, the round-trip reading kappa(y, (x c) y^-1 (x c)) has largest value rayKernel(x, y); the squared shifted reading (2 kappa(x c, y) - 1)^2 has the same largest value; and the integral over a full turn of the squared inner product of x (cos t + sin t i) with y equals pi times rayKernel(x, y). Put A = 2 kappa(x, y) - 1 and B = 2 kappa(x, y * i) - 1, so that rayKernel(x, y) = A^2 + B^2 by definition. For a phase c = a + b i one has 2 kappa(x c, y) - 1 = a A - b B, since right multiplication by a + b i mixes the inner products with y and with y * i. Over the circle a^2 + b^2 = 1 the square (a A - b B)^2 is at most A^2 + B^2 by the Cauchy-Schwarz inequality, with equality at a = A / r, b = -B / r for r the square root of A^2 + B^2, and at c = 1 when A = B = 0. For a unit quaternion p the round-trip identity kappa(y, p y^-1 p) = (2 kappa(p, y) - 1)^2 holds, because the real part of y^-1 p y^-1 p equals 2 <p, y>^2 - 1 for unit p and y; so the first set equals the second. Finally the squared inner product along the circle is A^2 cos^2 t + B^2 sin^2 t - 2 A B sin t cos t, whose integral over a full turn is pi (A^2 + B^2). Thus the ray kernel is both the fibre maximum of the round-trip reading and the mean of the squared inner product over the fibre, up to the factor pi; the module states no further property of the fibration.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.exists_homeomorph_quotient_phaseCircle`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.phaseCircle`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.range_hopf`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.rayKernel_isGreatest_and_integral`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionRayKernel](QuaternionRayKernel.md)
