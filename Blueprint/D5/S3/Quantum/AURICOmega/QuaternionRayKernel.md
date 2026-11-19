# The phase-blind ray kernel on the unit quaternions

## Abstract

The two-term squared reading of the quaternion comparison model depends only on the Hopf images, is blind to right phases in the span of 1 and i, and equals the trace pairing of two rank-one projections on complex two-space.

**Definition 1.1 (The Hopf image of a unit quaternion).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{hopf}\left(x\right) = x \cdot \operatorname{unitI} \cdot \operatorname{star}\left(x\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.hopf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Heinz Hopf (1931). *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*. DOI: [10.1007/BF01457962](https://doi.org/10.1007/BF01457962).

*Commentary.*

For a unit quaternion x the Hopf image is the quaternion x * i * star x, where i is the unit quaternion unitI and star x = x^-1. It is the image of i under conjugation by x, so it is an imaginary quaternion of norm one. Writing x = a + b i + c j + d k, its i, j and k components are a^2 + b^2 - c^2 - d^2, 2 (a d + b c) and 2 (b d - a c); these are quadratic forms whose squares add up to (a^2 + b^2 + c^2 + d^2)^2, so x -> hopf x maps the unit three-sphere into the unit two-sphere of imaginary quaternions. As Hopf observed, the map is onto and its fibres are great circles.

**Definition 1.2 (The two-term squared reading).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{rayKernel}\left(x, y\right) = \left(2 \cdot \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y\right) - 1\right)^{2} + \left(2 \cdot \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y \cdot \operatorname{unitI}\right) - 1\right)^{2}$$

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reading of the quaternion comparison model is kappa x y = (1 + <x, y>) / 2, so 2 * kappa x y - 1 is the real inner product <x, y>. The ray kernel adds its square to the square of the same expression after the second argument is multiplied on the right by i; thus rayKernel x y = <x, y>^2 + <x, y * i>^2.

**Theorem 1.3 (The ray kernel through the Hopf images).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{rayKernel}\left(x, y\right) = \frac{1 + \langle \operatorname{hopf}\left(x\right), \operatorname{hopf}\left(y\right) \rangle_{\mathbb{R}}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_eq_hopf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all quaternions p and q the polynomial identity <p, q>^2 + <p, q * i>^2 = (|p|^2 * |q|^2 + <p * i * star p, q * i * star q>) / 2 holds, as one checks by expanding both sides in the sixteen products of components. For unit quaternions |p| = |q| = 1, and the identity becomes the stated formula. In particular the ray kernel depends on x and y only through their Hopf images.

**Theorem 1.4 (Blindness to a phase on the left argument).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), c \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \left(\operatorname{imJ}\left(c\right) = 0 \land \operatorname{imK}\left(c\right) = 0\right) \Rightarrow \operatorname{rayKernel}\left(x \cdot c, y\right) = \operatorname{rayKernel}\left(x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_mul_phase_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quaternion c whose j and k components vanish lies in the real span of 1 and i and commutes with i. For a unit quaternion c of this kind, (x * c) * i * star (x * c) = x * (c * i * star c) * star x = x * i * star x, so right multiplication by c does not move the Hopf image. The formula through the Hopf images then gives the invariance.

**Theorem 1.5 (Blindness to a phase on the right argument).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), c \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \left(\operatorname{imJ}\left(c\right) = 0 \land \operatorname{imK}\left(c\right) = 0\right) \Rightarrow \operatorname{rayKernel}\left(x, y \cdot c\right) = \operatorname{rayKernel}\left(x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_mul_phase_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the same argument applied to the second argument: right multiplication of y by a unit quaternion c in the real span of 1 and i leaves the Hopf image of y unchanged.

**Theorem 1.6 (The ray kernel equals one exactly on the phase circles).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{rayKernel}\left(x, y\right) = 1 \Leftrightarrow \left(\exists c \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \left(\operatorname{imJ}\left(c\right) = 0 \land \operatorname{imK}\left(c\right) = 0\right) \land y = x \cdot c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Heinz Hopf (1931). *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*. DOI: [10.1007/BF01457962](https://doi.org/10.1007/BF01457962).

*Commentary.*

For all quaternions p and q the polynomial identity (star p * q)_j^2 + (star p * q)_k^2 = |p|^2 * |q|^2 - (<p, q>^2 + <p, q * i>^2) holds, where the subscripts denote the j and k components. If the ray kernel of the unit quaternions x and y equals one, the right side vanishes, so the j and k components of c = x^-1 * y = star x * y are both zero, as a sum of two squares that vanishes; and y = x * c. Conversely, if y = x * c with such a unit quaternion c, the phase invariance reduces the ray kernel to rayKernel x x = (1 + |hopf x|^2) / 2 = 1, since the Hopf image has norm one. It follows from this equivalence and the formula through the Hopf images, together with the equality case of the Cauchy-Schwarz inequality for the unit Hopf images, that two unit quaternions have the same Hopf image exactly when they differ by a right factor on the circle of unit quaternions in the span of 1 and i.

**Definition 1.7 (Quaternions as complex two-vectors).**

Lean statement: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.spinor`

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.spinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

spinor is the real-linear isometric equivalence from the real quaternions to the Euclidean space of complex pairs indexed by Fin 2 that sends a + b i + c j + d k to the pair (a + b I, -c + d I), where I is the complex unit. Its inverse sends a pair (u, w) to the quaternion with components re u, im u, -re w and im w. It preserves norms because |a + b I|^2 + |-c + d I|^2 = a^2 + b^2 + c^2 + d^2.

**Theorem 1.8 (The ray kernel as a trace pairing of rank-one projections).**

$$\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \left(\forall q \in \mathbb{H}[\mathbb{R}],\; \operatorname{spinor}\left(q \cdot \operatorname{unitI}\right) = I \cdot \operatorname{spinor}\left(q\right)\right) \land \left(\operatorname{bloch}\left(\operatorname{vecMulVec}\left(\operatorname{ofLp}\left(\operatorname{spinor}\left(x\right)\right), \operatorname{star}\left(\operatorname{ofLp}\left(\operatorname{spinor}\left(x\right)\right)\right)\right)\right) = \operatorname{toLp}\left(2, (\operatorname{imK}\left(\operatorname{hopf}\left(x\right)\right), \operatorname{imJ}\left(\operatorname{hopf}\left(x\right)\right), \operatorname{imI}\left(\operatorname{hopf}\left(x\right)\right))\right) \land \left(\operatorname{rayKernel}\left(x, y\right) = \left\lVert \operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{ofLp}\left(\operatorname{spinor}\left(x\right)\right)\right), \operatorname{ofLp}\left(\operatorname{spinor}\left(y\right)\right)\right) \right\rVert^{2} \land \operatorname{ofReal}\left(\operatorname{rayKernel}\left(x, y\right)\right) = \operatorname{bornProbability}\left(\operatorname{vecMulVec}\left(\operatorname{ofLp}\left(\operatorname{spinor}\left(y\right)\right), \operatorname{star}\left(\operatorname{ofLp}\left(\operatorname{spinor}\left(y\right)\right)\right)\right), \operatorname{vecMulVec}\left(\operatorname{ofLp}\left(\operatorname{spinor}\left(x\right)\right), \operatorname{star}\left(\operatorname{ofLp}\left(\operatorname{spinor}\left(x\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_eq_bornProbability_spinor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display ofLp is the coordinate vector of a point of the Euclidean space, vecMulVec v (star v) is the rank-one matrix with entries v a * conj (v b), dotProduct is the bilinear sum of products of coordinates, ofReal regards a real number as a complex number, and the Bloch vector of a complex two-by-two matrix M is (2 re M01, -2 im M01, re M00 - re M11). The four conjuncts hold for all unit quaternions x and y. First, multiplying q on the right by i multiplies the image pair by the complex unit, which is a direct computation in components. Second, the Bloch vector of the rank-one projection onto the image of x has coordinates the k, j and i components of the Hopf image of x, again by expanding both sides; since spinor x is a unit vector, this is the expression that the Bloch vector of a pure state takes, so together with the unit norm of Bloch vectors of pure states this identity implies that the coordinate vector of the Hopf image has norm one. Third, the complex transition amplitude star (spinor x) . spinor y has real part <x, y> and imaginary part -<x, y * i>, so its squared modulus is the ray kernel. Fourth, the trace of the product of the two rank-one projections onto spinor y and spinor x is the squared modulus of that amplitude, by the reduction of a rank-one branch weight on a rank-one pure state to a squared transition modulus.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.hopf`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_eq_bornProbability_spinor`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_eq_hopf`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_eq_one_iff`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_mul_phase_left`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.rayKernel_mul_phase_right`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionRayKernel.spinor`
- Dependency: [D5/S3/Observer/BornReduction](../../Observer/BornReduction.md)
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
