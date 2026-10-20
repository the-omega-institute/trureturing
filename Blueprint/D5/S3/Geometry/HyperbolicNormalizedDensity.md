# Native Hausdorff density

## Abstract

Native Hausdorff three-measure and its coordinate density.

Coordinates3 is UpperHalfSpace over Complex: the positive-height subtype of the Euclidean space WithLp 2 (Complex times Real). Native3 is HyperbolicThreeSpace. If D is Euclidean coordinate distance and hx, hy are the two positive heights, native distance is 2 arsinh(D/(2 sqrt(hx hy))). Both spaces have their Borel measurable structures; in the formulas, borel and BorelSpace denote this choice and its compatibility with the topology.

$$
Coordinates3 = \operatorname{UpperHalfSpace}\left(Complex\right)
$$

$$
Native3 = HyperbolicThreeSpace
$$

$$
\operatorname{measurableSpace}\left(Coordinates3\right) = \operatorname{borel}\left(Coordinates3\right)
$$

$$
\operatorname{BorelSpace}\left(Coordinates3\right)
$$

$$
\operatorname{measurableSpace}\left(Native3\right) = \operatorname{borel}\left(Native3\right)
$$

$$
\operatorname{BorelSpace}\left(Native3\right)
$$

coordinatesEquiv is the measurable equivalence underlying the coordinate homeomorphism. It sends a native point to its coordinates, and its inverse is the constructor mk.

$$
coordinatesEquiv = \operatorname{toMeasurableEquiv}\left(\operatorname{coordinatesHomeomorph}\left(Complex\right)\right)
$$

$$
\forall z \in Native3,\; \operatorname{coordinatesEquiv}\left(z\right) = \operatorname{coordinates}\left(z\right)
$$

$$
\forall s \in \operatorname{Set}\left(Coordinates3\right),\; \operatorname{preimage}\left(coordinatesEquiv, s\right) = \operatorname{image}\left(mk, s\right)
$$

The two raw measures are Mathlib's unnormalized Hausdorff three-measures on their respective metric spaces. heightDensity takes values in the extended nonnegative reals; ofReal is the canonical map from real numbers to that space.

$$
rawCoordinateMeasure = \operatorname{hausdorffMeasure}\left(3, Coordinates3\right)
$$

$$
rawNativeMeasure = \operatorname{hausdorffMeasure}\left(3, Native3\right)
$$

$$
\forall x \in Coordinates3,\; \operatorname{heightDensity}\left(x\right) = \operatorname{ofReal}\left(\operatorname{inv}\left(\operatorname{height}\left(x\right)\right)^{3}\right)
$$

**Theorem 1.1 (Raw Hausdorff density identity).**

$$\operatorname{map}\left(rawNativeMeasure, coordinatesEquiv\right) = \operatorname{withDensity}\left(rawCoordinateMeasure, heightDensity\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicNormalizedDensity.raw_native_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here map denotes measure pushforward, and withDensity denotes multiplication of a measure by a nonnegative measurable density through the lower integral. The equality has no hypotheses and is an equality of measures, including sets with zero or infinite measure. The two sides use the original native and coordinate metrics. The argument combines local metric distortion, pointwise height bounds, countable additivity and an extended-real limit.

For a positive radius below the height of its centre, local Hausdorff comparison and the preimage identity above give the following bounds on each Borel subset of the coordinate ball. Every ball in this exposition uses the Euclidean coordinate metric.

$$
\forall p \in Coordinates3,\; \forall r \in Real,\; \left(0 < r \land r < \operatorname{height}\left(p\right)\right) \Rightarrow \left(\forall s \in \operatorname{Set}\left(Coordinates3\right),\; \left(\operatorname{MeasurableSet}\left(s\right) \land s \subseteq \operatorname{ball}\left(p, r\right)\right) \Rightarrow \left(\operatorname{mass}\left(rawCoordinateMeasure, s\right) \le \operatorname{ofReal}\left(\operatorname{height}\left(p\right) + 2 \cdot r\right)^{3} \cdot \operatorname{mass}\left(\operatorname{map}\left(rawNativeMeasure, coordinatesEquiv\right), s\right) \land \operatorname{mass}\left(\operatorname{map}\left(rawNativeMeasure, coordinatesEquiv\right), s\right) \le \operatorname{ofReal}\left(\operatorname{inv}\left(\operatorname{height}\left(p\right) - r\right)\right)^{3} \cdot \operatorname{mass}\left(rawCoordinateMeasure, s\right)\right)\right)
$$

Define the distortion factor for real epsilon by the formula below. For zero less than epsilon less than one, pointwise bounds on height over a ball of radius epsilon times the centre height bound the density from above and below. Combining these bounds with local Hausdorff comparison yields the two inequalities with the same factor.

$$
\forall epsilon \in Real,\; \operatorname{distortionFactor}\left(epsilon\right) = \operatorname{ofReal}\left((\frac{1 + 2 \cdot epsilon}{1 - epsilon})^{3}\right)
$$

$$
\forall epsilon \in Real,\; \left(0 < epsilon \land epsilon < 1\right) \Rightarrow \left(\forall p \in Coordinates3,\; \forall s \in \operatorname{Set}\left(Coordinates3\right),\; \left(\operatorname{MeasurableSet}\left(s\right) \land s \subseteq \operatorname{ball}\left(p, epsilon \cdot \operatorname{height}\left(p\right)\right)\right) \Rightarrow \left(\operatorname{mass}\left(\operatorname{withDensity}\left(rawCoordinateMeasure, heightDensity\right), s\right) \le \operatorname{distortionFactor}\left(epsilon\right) \cdot \operatorname{mass}\left(\operatorname{map}\left(rawNativeMeasure, coordinatesEquiv\right), s\right) \land \operatorname{mass}\left(\operatorname{map}\left(rawNativeMeasure, coordinatesEquiv\right), s\right) \le \operatorname{distortionFactor}\left(epsilon\right) \cdot \operatorname{mass}\left(\operatorname{withDensity}\left(rawCoordinateMeasure, heightDensity\right), s\right)\right)\right)
$$

These balls cover Coordinates3. A Lindelof countable subcover can be disjointified into Borel pieces Dn. For a Borel set s, the sets s intersect Dn form a countable measurable partition of s. Applying the local estimates to each piece and summing in the extended nonnegative reals gives the global bounds.

$$
\forall epsilon \in Real,\; \left(0 < epsilon \land epsilon < 1\right) \Rightarrow \left(\forall s \in \operatorname{Set}\left(Coordinates3\right),\; \operatorname{MeasurableSet}\left(s\right) \Rightarrow \left(\operatorname{mass}\left(\operatorname{withDensity}\left(rawCoordinateMeasure, heightDensity\right), s\right) \le \operatorname{distortionFactor}\left(epsilon\right) \cdot \operatorname{mass}\left(\operatorname{map}\left(rawNativeMeasure, coordinatesEquiv\right), s\right) \land \operatorname{mass}\left(\operatorname{map}\left(rawNativeMeasure, coordinatesEquiv\right), s\right) \le \operatorname{distortionFactor}\left(epsilon\right) \cdot \operatorname{mass}\left(\operatorname{withDensity}\left(rawCoordinateMeasure, heightDensity\right), s\right)\right)\right)
$$

Take epsilon(n)=1/(n+2) for natural n. The distortion factors tend to one. For every fixed extended nonnegative real b, their products with b tend to b: multiplication is continuous at the nonzero limiting factor even if b is infinite. Closedness of the order relation therefore turns the two global inequalities into equality on every Borel set, which determines equality of measures.

An application is the usual Euclidean volume normalization. In the same L2 ambient space A, let Q be the parallelepiped of the standard real orthonormal basis, c3 its raw Hausdorff three-mass, j the coordinate subtype inclusion, and coordinateHaar the pullback of canonical ambient volume along j.

$$
A = \operatorname{WithLp}\left(2, \operatorname{Product}\left(Complex, Real\right)\right)
$$

$$
Q = \operatorname{parallelepiped}\left(\operatorname{toBasis}\left(\operatorname{stdOrthonormalBasis}\left(Real, A\right)\right)\right)
$$

$$
c3 = \operatorname{mass}\left(\operatorname{hausdorffMeasure}\left(3, A\right), Q\right)
$$

$$
j = subtypeVal
$$

$$
coordinateHaar = \operatorname{comap}\left(\operatorname{volume}\left(A\right), j\right)
$$

The real dimension of A is three. Its raw Hausdorff measure is an additive Haar measure. Haar uniqueness and orthonormal-cube calibration identify it with c3 times canonical volume. The cube has nonempty interior and is compact, so c3 is strictly positive and finite. The inclusion j is isometric and an open measurable embedding, giving the coordinate calibration below.

$$
0 < c3 \land c3 < \infty
$$

$$
\operatorname{hausdorffMeasure}\left(3, A\right) = \operatorname{smul}\left(c3, \operatorname{volume}\left(A\right)\right)
$$

$$
rawCoordinateMeasure = \operatorname{smul}\left(c3, coordinateHaar\right)
$$

Substituting this calibration into the raw identity and cancelling c3 once gives the normalized formula. No set mass is divided out, and no sup-norm Hausdorff measure is substituted for the L2 measure.

$$
\operatorname{map}\left(\operatorname{smul}\left(\operatorname{inv}\left(c3\right), rawNativeMeasure\right), coordinatesEquiv\right) = \operatorname{withDensity}\left(coordinateHaar, heightDensity\right)
$$

Natural-dimension application of the same local-distortion and squeeze argument. For every natural d, let Hcoord_d and Hnative_d be raw Hausdorff d-measure in the unchanged Euclidean coordinate and native H3 metrics. Then map(Hnative_d,coordinatesEquiv)=withDensity(Hcoord_d,x |-> ofReal(height(x)^(-d))). In the local Hausdorff image inequalities, use the original ball_distortion with powers d; on a ball of radius epsilon*height(p), the common density distortion factor is ((1+2*epsilon)/(1-epsilon))^d. The same countable Borel partition and extended-real squeeze prove the equality, including d=0 and sets of infinite measure.

For d=2 this identifies the native H3 surface-dimension measure with height^(-2) times ambient Euclidean-coordinate Hausdorff two-measure. Ambient three-dimensional Hausdorff two-measure is not assumed sigma-finite: the argument evaluates withDensity only on Borel sets, uses countable additivity with values in the extended nonnegative reals, and cancels only finite positive local distortion scalars. This application does not replace that coordinate two-measure by three-dimensional volume, or identify it with dxdy on a specified plane. A plane-area formula still needs the actual Euclidean embedding, an independent dimension-two Euclidean calibration and isometric measure transport; the c3 normalization above supplies none of those identifications.

The density identity concerns measures on the whole upper half-space. It gives no Gram-map Jacobian, frame-independence statement, finite positive mass for a specified geometric body, Schlaefli variation formula or strictly positive flat-boundary limit.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicNormalizedDensity.raw_native_density`
- Dependency: [D5/S3/Geometry/HyperbolicHausdorffComparison](HyperbolicHausdorffComparison.md)
- Dependency: [D5/S3/Geometry/HyperbolicTopology](HyperbolicTopology.md)
