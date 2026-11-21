# One-point extensions of the unit-quaternion reading

## Abstract

Adding one point with self-reading d to the unit quaternions keeps the Gram forms of the reading kappa x y = (1 + <x, y>) / 2 nonnegative exactly when the new readings are (a + <b, x>) / sqrt 2 with a^2 + |b|^2 <= d, and it suffices to test six points; feature rank five forces a^2 + |b|^2 = 1; and the extensions that reach the value one, or, when nonnegative of feature rank five, the value zero, are exactly the readings of points already present.

**Definition 1.1 (One-point extensions of feature rank r).**

$$\forall f \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to \mathbb{R},\; \forall r \in \mathbb{N},\; \operatorname{HasOnePointFeatureRank}\left(f, r\right) \Leftrightarrow \left(\exists v \in \operatorname{Option}\left(\operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right)\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(r\right)\right),\; \left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), y \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \operatorname{kappa}\left(\operatorname{quaternionModel}, x, y\right) = \langle v\left(\operatorname{some}\left(x\right)\right), v\left(\operatorname{some}\left(y\right)\right) \rangle_{\mathbb{R}}\right) \land \left(\left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; f\left(x\right) = \langle v\left(\operatorname{some}\left(x\right)\right), v\left(\operatorname{none}\right) \rangle_{\mathbb{R}}\right) \land \left\lVert v\left(\operatorname{none}\right) \right\rVert = 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.HasOnePointFeatureRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A function f on the unit quaternions is read as the readings of one new point against the points of the unit quaternion comparison model. The extension has feature rank r when there is a map v from the unit quaternions with one extra point none into Euclidean r-space such that the inner products of the images of old points are the model readings, the inner product of the image of an old point x with the image of the new point is f(x), and the new point is sent to a unit vector. The unit norm says that the new point reads one against itself. In the Lean statement the map is called phi.

**Lemma 1.2 (Nonnegative affine readings).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{H}[\mathbb{R}],\; \left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; 0 \le \frac{a + \langle b, x \rangle_{\mathbb{R}}}{\sqrt{2}}\right) \Leftrightarrow \left\lVert b \right\rVert \le a$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.forall_nonneg_iff_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real number a and a quaternion b, the affine readings (a + <b, x>) / sqrt 2 are nonnegative at every unit quaternion x exactly when |b| <= a. By the Cauchy-Schwarz inequality <b, x> >= -|b| for a unit quaternion x, and the value -|b| is attained at x = -b / |b| (at any unit quaternion when b = 0), so the minimum of the readings is (a - |b|) / sqrt 2.

**Theorem 1.3 (Positive semidefinite one-point extensions are affine).**

$$\forall f \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to \mathbb{R},\; \forall d \in \mathbb{R},\; \operatorname{List.TFAE}([\left(\forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall c \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; 0 \le d \cdot t^{2} + 2 \cdot t \cdot \sum_{i \in \operatorname{Fin}\left(n\right)} \left(c\left(i\right) \cdot f\left(x\left(i\right)\right)\right) + \sum_{i \in \operatorname{Fin}\left(n\right)} \left(\sum_{j \in \operatorname{Fin}\left(n\right)} \left(c\left(i\right) \cdot c\left(j\right) \cdot \operatorname{kappa}\left(\operatorname{quaternionModel}, x\left(i\right), x\left(j\right)\right)\right)\right)\right), \left(\forall x \in \operatorname{Fin}\left(6\right) \to \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall c \in \operatorname{Fin}\left(6\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; 0 \le d \cdot t^{2} + 2 \cdot t \cdot \sum_{i \in \operatorname{Fin}\left(6\right)} \left(c\left(i\right) \cdot f\left(x\left(i\right)\right)\right) + \sum_{i \in \operatorname{Fin}\left(6\right)} \left(\sum_{j \in \operatorname{Fin}\left(6\right)} \left(c\left(i\right) \cdot c\left(j\right) \cdot \operatorname{kappa}\left(\operatorname{quaternionModel}, x\left(i\right), x\left(j\right)\right)\right)\right)\right), \left(\exists a \in \mathbb{R},\; \exists b \in \mathbb{H}[\mathbb{R}],\; a^{2} + \left\lVert b \right\rVert^{2} \le d \land \left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; f\left(x\right) = \frac{a + \langle b, x \rangle_{\mathbb{R}}}{\sqrt{2}}\right)\right)])$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.tfae_onePointExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Aronszajn (1950). *Theory of reproducing kernels*. DOI: [10.1090/S0002-9947-1950-0051437-7](https://doi.org/10.1090/S0002-9947-1950-0051437-7).

*Commentary.*

Extending the reading of the unit quaternions by one new point with readings f(x) against the old points and self-reading d gives, for weights c on finitely many old points x and the weight t on the new point, the Gram form d * t^2 + 2 * t * sum c(i) * f(x(i)) + sum sum c(i) * c(j) * kappa(x(i), x(j)). Three conditions are equivalent. The first says that all these forms are nonnegative, for every finite family of old points. The second says the same only for families of exactly six old points, which may repeat. The third says that f(x) = (a + <b, x>) / sqrt 2 for a real number a and a quaternion b with a^2 + |b|^2 <= d. The first condition contains the second. The Gram form of the old points alone is half of the squared total weight plus half of the squared norm of the weighted sum of the points, since kappa(x, y) = (1 + <x, y>) / 2. If f is affine with the stated bound, the extended form is half of (s + sqrt 2 * t * a)^2 + |q + sqrt 2 * t * b|^2 plus t^2 * (d - a^2 - |b|^2), where s is the total weight and q the weighted sum, and so it is nonnegative for every finite family; this gives the first condition from the third. From the second: every unit quaternion y is a combination of the five points 1, -1, i, j and k with total weight one and weighted sum y. The six-point family of y with weight -1 and of these five points with those weights has total weight zero and weighted sum zero, so its Gram form vanishes; a form that is nonnegative for every t and has no quadratic part in the old weights must then have zero linear part, so f(y) is the same combination of f(1), f(-1), f(i), f(j) and f(k), which makes f affine in the coordinates of y. The six-point family of the five points with total weight -sqrt 2 * a and weighted sum -sqrt 2 * b, padded by the point 1 with weight zero, together with t = 1, has Gram form d - a^2 - |b|^2, which gives the bound. So nonnegativity needs to be tested on families of six points only; whether fewer points suffice is not decided here. No sign condition on d is assumed; for negative d the first and third conditions fail. The equivalence of the first and third conditions is related to the theory of reproducing kernels: for a positive semidefinite kernel, the functions whose one-point extension stays positive semidefinite are those of the associated Hilbert space of functions, with the bound on d read as a bound on the squared norm; for the quaternion reading that space consists of the affine functions a + <b, x>. Only this relation is recorded here; the statement and its proof above do not rest on that theory.

**Theorem 1.4 (One-point extensions of feature rank five).**

$$\forall f \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to \mathbb{R},\; \operatorname{HasOnePointFeatureRank}\left(f, 5\right) \Leftrightarrow \left(\exists a \in \mathbb{R},\; \exists b \in \mathbb{H}[\mathbb{R}],\; a^{2} + \left\lVert b \right\rVert^{2} = 1 \land \left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; f\left(x\right) = \frac{a + \langle b, x \rangle_{\mathbb{R}}}{\sqrt{2}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.hasOnePointFeatureRank_five_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A function f on the unit quaternions is a one-point extension of feature rank five exactly when f(x) = (a + <b, x>) / sqrt 2 with a^2 + |b|^2 = 1. No sign condition on the readings is involved. A realization in Euclidean five-space has nonnegative extended Gram forms with self-reading one, so the previous theorem with d = 1 makes f affine with a^2 + |b|^2 <= 1. The reading of the unit quaternions itself has feature rank at least five, so the images of the old points span Euclidean five-space and the unit vector of the new point is a combination of them. Applying the Gram identity of the previous theorem to that combination and the Cauchy-Schwarz inequality for <b, q> gives a^2 + |b|^2 >= 1. Conversely, the vector (a, b) of Euclidean five-space is a unit vector when a^2 + |b|^2 = 1, and its inner product with the feature (1, x) / sqrt 2 of x is (a + <b, x>) / sqrt 2. Together with the nonnegativity criterion, the nonnegative extensions of feature rank five are those with |b| <= a and a^2 + |b|^2 = 1.

**Theorem 1.5 (Extensions that reach one are old points).**

$$\forall f \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to \mathbb{R},\; \left(\forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall c \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; 0 \le t^{2} + 2 \cdot t \cdot \sum_{i \in \operatorname{Fin}\left(n\right)} \left(c\left(i\right) \cdot f\left(x\left(i\right)\right)\right) + \sum_{i \in \operatorname{Fin}\left(n\right)} \left(\sum_{j \in \operatorname{Fin}\left(n\right)} \left(c\left(i\right) \cdot c\left(j\right) \cdot \operatorname{kappa}\left(\operatorname{quaternionModel}, x\left(i\right), x\left(j\right)\right)\right)\right)\right) \Rightarrow \left(\left(\exists u \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; f\left(u\right) = 1\right) \Leftrightarrow \left(\exists w \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; f\left(x\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, x, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.exists_eq_one_iff_exists_eq_kappa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f have nonnegative extended Gram forms with self-reading one. Then f takes the value one at some unit quaternion exactly when f is the reading kappa(x, x0) of some unit quaternion x0. No rank or sign condition is needed. By the extension theorem f(x) = (a + <b, x>) / sqrt 2 with a^2 + |b|^2 <= 1. A value one at x1 forces sqrt 2 <= a + |b|, while (a + |b|)^2 <= 2 * (a^2 + |b|^2) <= 2, so a = |b| = 1 / sqrt 2 and <b, x1> = |b|; the equality case of the Cauchy-Schwarz inequality gives b = x1 / sqrt 2, and f is the reading of x1. Conversely, the reading of x0 is one at x0. The positivity hypothesis is needed: the constant one takes the value one but is not the reading of any point, since the reading of x0 vanishes at -x0. In the display the points x1 and x0 of the Lean statement are written u and w.

**Theorem 1.6 (Nonnegative rank-five extensions that reach zero are old points).**

$$\forall f \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \to \mathbb{R},\; \operatorname{HasOnePointFeatureRank}\left(f, 5\right) \Rightarrow \left(\left(\forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; 0 \le f\left(x\right)\right) \Rightarrow \left(\left(\exists u \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; f\left(u\right) = 0\right) \Leftrightarrow \left(\exists w \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; f\left(x\right) = \operatorname{kappa}\left(\operatorname{quaternionModel}, x, w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.exists_eq_zero_iff_exists_eq_kappa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a nonnegative one-point extension of feature rank five. Then f takes the value zero at some unit quaternion exactly when f is the reading kappa(x, x0) of some unit quaternion x0. By the rank-five classification f(x) = (a + <b, x>) / sqrt 2 with a^2 + |b|^2 = 1, and by the nonnegativity criterion |b| <= a. A zero at x1 forces <b, x1> = -a <= -|b|, so a = |b| = 1 / sqrt 2 and <b, -x1> = |b|; the equality case of the Cauchy-Schwarz inequality gives b = -x1 / sqrt 2, and f is the reading of -x1. Conversely, the reading of x0 is zero at -x0. Both hypotheses are needed. The readings <1, x> / sqrt 2 (a = 0, b = 1) have feature rank five and vanish at i, but take the negative value -1 / sqrt 2 at -1, so they are not the readings of a point. The readings (1 / 2 + <b, x>) / sqrt 2 with b = 1 / 2 are nonnegative, have nonnegative extended Gram forms with self-reading one and vanish at -1, but never reach the value one, so they are not the readings of a point, and by this theorem they do not have feature rank five. Taken with the rank-five classification, the unit quaternions cannot be enlarged by a point whose readings reach zero without raising the feature rank above five or taking negative values, and not by a point whose readings reach one at all. In the display the points x1 and x0 of the Lean statement are written u and w.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.HasOnePointFeatureRank`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.exists_eq_one_iff_exists_eq_kappa`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.exists_eq_zero_iff_exists_eq_kappa`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.forall_nonneg_iff_norm_le`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.hasOnePointFeatureRank_five_iff`
- Truth anchor: `D5/S3/Quantum/AURICOmega/QuaternionReadingOnePointExtension.tfae_onePointExtension`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonRankFive](TernaryComparisonRankFive.md)
