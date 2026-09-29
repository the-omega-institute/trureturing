# Infinite Calibration Sets for Analytic Scalar Controls

## Abstract

One positive real parameter gives a strictly feasible analytic scalar control whose simultaneous value and derivative calibration points are exactly the positive-natural sequence converging to one.

All scalar parameters are real. Assume 0 < a < 1, 0 < delta, delta < (1-a)/4, delta < (1-a squared)/16, and 0 < b < 1-a/(1-delta). The delta bound involving a squared is retained even though it is not needed in the scalar argument. The domain of physicality and calibration is the open interval (a,1).

Use the scalar parameters L(a)=1-a, lam(a,delta)=L(a)-delta, gamma(a,delta)=lam(a,delta)/(2 delta), and center(a,delta)=lam(a,delta)/L(a). The radius is sqrt(a/lam(a,delta)) times sqrt((1-p)/p). The energy at s is s squared plus gamma squared times (s+1/s-2) squared, and beta(p)=1/(2 p (1-p)). Division uses total real inversion; all denominators used on the stated interval are nonzero.

**Definition 1.1 (The oscillatory phase).**

$$\forall b, p: \mathbb{R}, \operatorname{omega}\left(b, p\right) = \frac{2 \pi b}{1 - p}$$

*Formalization.* `D5/S3/Quantum/Information/InfiniteCalibrationControl.omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive b the phase increases without bound as p approaches one from below.

**Definition 1.2 (The decaying amplitude).**

$$\forall b, p: \mathbb{R}, \operatorname{amplitude}\left(b, p\right) = \frac{1 - p}{4 \pi b p}$$

*Formalization.* `D5/S3/Quantum/Information/InfiniteCalibrationControl.amplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b > 0 and 0 < p < 1 the amplitude is positive. It tends to zero as p tends to one.

**Definition 1.3 (The oscillatory interpolant).**

$$\forall b, p: \mathbb{R}, \operatorname{phaseH}\left(b, p\right) = 1 + \operatorname{amplitude}\left(b, p\right) \operatorname{sin}\left(\operatorname{omega}\left(b, p\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bounded sine factor and decaying amplitude make this interpolant tend to one at the upper endpoint.

**Definition 1.4 (The nonnegative damping factor).**

$$\forall b, p: \mathbb{R}, \operatorname{phaseD}\left(b, p\right) = {\operatorname{sin}\left(\frac{1}{2} \operatorname{omega}\left(b, p\right)\right)}^{2}$$

*Formalization.* `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The damping factor is a square. Below one, with b positive, it vanishes exactly at points 1-b/n with n a positive natural number.

**Definition 1.5 (The scalar control).**

$$\forall a, delta, b, k, p: \mathbb{R}, \operatorname{phaseControl}\left(a, delta, b, k, p\right) = \frac{\operatorname{phaseH}\left(b, p\right) + k \operatorname{center}\left(a, delta\right) \operatorname{phaseD}\left(b, p\right)}{1 + k \operatorname{phaseD}\left(b, p\right)}$$

*Formalization.* `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When k is positive the denominator is at least one. The control is a convex combination of the interpolant and the fixed center, with interpolant weight 1/(1+k phaseD(b,p)).

**Definition 1.6 (The positive-natural calibration sequence).**

$$\forall b: \mathbb{R}, \forall n: \mathbb{N}, \operatorname{phaseNode}\left(b, n\right) = 1 - \frac{b}{n}$$

*Formalization.* `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseNode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition is total on natural numbers. Only positive indices occur in the calibration set. Under the parameter hypotheses, these nodes lie above a/(1-delta), are strictly increasing, and converge to one.

**Definition 1.7 (All scalar control requirements for the same parameter).**

$$\forall a, delta, b, k: \mathbb{R}, \operatorname{InfiniteScalarControl}\left(a, delta, b, k\right) \iff (0 < k \land (\forall p \in \operatorname{Ioo}\left(a, 1\right), (0 < \operatorname{phaseControl}\left(a, delta, b, k, p\right) \land {\operatorname{radius}\left(a, delta, p\right)}^{2} \operatorname{energy}\left(a, delta, \operatorname{phaseControl}\left(a, delta, b, k, p\right)\right) < 1)) \land \operatorname{AnalyticOnNhd}\left(\mathbb{R}, \operatorname{phaseControl}\left(a, delta, b, k\right), \operatorname{Ioo}\left(a, 1\right)\right) \land (\forall p \in \operatorname{Ioo}\left(a, 1\right), ((\operatorname{phaseControl}\left(a, delta, b, k, p\right) = 1 \land \operatorname{deriv}\left(\operatorname{phaseControl}\left(a, delta, b, k\right), p\right) = \operatorname{beta}\left(p\right)) \iff (\exists n: \mathbb{N}, 0 < n \land p = \operatorname{phaseNode}\left(b, n\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/InfiniteCalibrationControl.InfiniteScalarControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conjunction requires k > 0, positivity and strict physicality at every point of (a,1), analyticity in a neighborhood of each point of that interval, and the complete simultaneous jet characterization. Value one alone does not characterize the nodes: the derivative must also equal beta at the same point.

**Theorem 1.8 (One finite parameter realizes the entire infinite calibration set).**

$$\forall a, delta, b: \mathbb{R}, (0 < a \land a < 1 \land 0 < delta \land delta < \frac{1 - a}{4} \land delta < \frac{1 - {a}^{2}}{16} \land 0 < b \land b < 1 - \frac{a}{1 - delta}) \Rightarrow \exists k: \mathbb{R}, (0 < k \land (\forall p \in \operatorname{Ioo}\left(a, 1\right), (0 < \operatorname{phaseControl}\left(a, delta, b, k, p\right) \land {\operatorname{radius}\left(a, delta, p\right)}^{2} \operatorname{energy}\left(a, delta, \operatorname{phaseControl}\left(a, delta, b, k, p\right)\right) < 1)) \land \operatorname{AnalyticOnNhd}\left(\mathbb{R}, \operatorname{phaseControl}\left(a, delta, b, k\right), \operatorname{Ioo}\left(a, 1\right)\right) \land (\forall p \in \operatorname{Ioo}\left(a, 1\right), ((\operatorname{phaseControl}\left(a, delta, b, k, p\right) = 1 \land \operatorname{deriv}\left(\operatorname{phaseControl}\left(a, delta, b, k\right), p\right) = \operatorname{beta}\left(p\right)) \iff (\exists n: \mathbb{N}, 0 < n \land p = \operatorname{phaseNode}\left(b, n\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/InfiniteCalibrationControl.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The center lies strictly between three quarters and one and is strictly feasible throughout [a,1]. The energy is convex on the positive half-line. Near one, the interpolant tends to one and radius squared times its energy tends to zero. This gives a whole terminal interval where every positive k is feasible by convexity.

On the remaining compact interval, zeros of the damping factor give value one above the strict feasibility threshold. At every other point, increasing k makes the control tend to the strictly feasible center. The open sets of feasible points increase with k; a directed compactness argument selects one positive real k for the entire complement. Together these intervals give full physicality on (a,1).

Analyticity holds for every positive k because the constituent functions are analytic on (a,1) and the denominator is positive. The half-phase sine vanishes exactly at the positive-natural nodes. At these zeros the control has value one and derivative beta. At any other point where the control equals one, differentiation and the double-angle identities give a strictly negative derivative. Since beta is positive on the interval, such extra roots cannot be calibration jets. These conclusions apply to the same k chosen for physicality.

## References

- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.InfiniteScalarControl`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.amplitude`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.omega`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseControl`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseD`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseH`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.phaseNode`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.result`
- Dependency: [D5/S3/Quantum/Information/FiniteCalibrationControl](FiniteCalibrationControl.md)
