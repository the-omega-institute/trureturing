# The Mittag-Leffler Barnes kernel

## Abstract

The literal Barnes kernel is integrable on exterior vertical contours.

**Definition 1.1 (The literal Barnes kernel).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall s \in Complex,\; kernel\left(alpha, beta, z, s\right) = (((ComplexGamma\left(s\right)*ComplexGamma\left((1-s)\right))*\frac{1}{ComplexGamma\left((beta-(alpha*s))\right)})*exp\left((-(s)*log\left(-(z)\right))\right))$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

ComplexGamma is complex Gamma, log is the principal complex logarithm, and all real scalars are embedded into Complex. The formula uses the entire reciprocal Gamma, including its zeros.

**Definition 1.2 (The angular margin).**

$$\forall alpha \in Real,\; \forall z \in Complex,\; margin\left(alpha, z\right) = ((\pi *(1-\frac{alpha}{2}))-\left|arg\left(-(z)\right)\right|)$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.margin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The strict exterior sector is exactly the set where margin(alpha,z) is positive.

**Theorem 1.3 (A majorant on a vertical line).**

$$\forall alpha \in Real,\; 0 < alpha \Rightarrow \left(\forall beta \in Real,\; \forall c \in Real,\; \forall z \in Complex,\; sin\left((\pi *c)\right)\neq 0 \Rightarrow \left(\exists C \in Real,\; \exists K \in Nat,\; \forall y \in Real,\; \left\lVert kernel\left(alpha, beta, z, (c+(y*\operatorname{ComplexI}))\right) \right\rVert \le ((C*(1+\left|y\right|)^{K})*exp\left(-((margin\left(alpha, z\right)*\left|y\right|))\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.exists_line_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

For alpha positive and a real line c with sin(pi*c) nonzero, the constants C and K are independent of the line coordinate y. Reflection converts the two Gamma factors into pi/sin(pi*s), leaving the reciprocal Gamma bound and the exact principal-logarithm exponential norm. No series representation is assumed.

**Theorem 1.4 (Integrability in the strict exterior sector).**

$$\forall alpha \in Real,\; 0 < alpha \Rightarrow \left(\forall beta \in Real,\; \forall c \in Real,\; \forall z \in Complex,\; sin\left((\pi *c)\right)\neq 0 \Rightarrow \left(0 < margin\left(alpha, z\right) \Rightarrow Integrable\left((y:Real \mapsto kernel\left(alpha, beta, z, (c+(y*\operatorname{ComplexI}))\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.integrable_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The polynomial-exponential majorant is integrable when the angular margin is positive. The reflected expression is measurable because reciprocal Gamma is entire; division by sine is a measurable operation.

**Definition 1.5 (The left contour sequence).**

$$\forall n \in Nat,\; leftLine\left(n\right) = (\frac{1}{2}-n)$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.leftLine` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The line indexed by n has real part one half minus n.

**Definition 1.6 (The shifted Gamma numerator).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall n \in Nat,\; \forall s \in Complex,\; leftNumerator\left(alpha, beta, z, n, s\right) = \frac{(((ComplexGamma\left((1-s)\right)*\frac{1}{ComplexGamma\left((beta-(alpha*s))\right)})*exp\left((-(s)*log\left(-(z)\right))\right))*ComplexGamma\left(((s+n)+1)\right))}{product\left(range\left(n\right), (j:Nat \mapsto (s+j))\right)}$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.leftNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The finite product contains precisely the factors s+j with j<n. Each zero lies strictly to the right of the n-th closed strip. The shifted Gamma and Gamma(1-s) have positive real arguments on that strip. Reciprocal Gamma is entire, including at its zeros.

**Theorem 1.7 (Holomorphy on the closed strip).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall n \in Nat,\; DifferentiableOn\left(Complex, (s:Complex \mapsto leftNumerator\left(alpha, beta, z, n, s\right)), preimage\left(re, Icc\left(leftLine\left((n+1)\right), leftLine\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.differentiableOn_leftNumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The two ordinary Gamma factors avoid all their poles by their positive real parts. The finite factors divided out do not vanish on the strip. Differentiability of reciprocal Gamma supplies the remaining factor without any denominator nonvanishing hypothesis.

**Theorem 1.8 (The actual single-pole factorization).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall n \in Nat,\; \forall s \in Complex,\; \left(mem\left(re\left(s\right), Icc\left(leftLine\left((n+1)\right), leftLine\left(n\right)\right)\right) \land s\neq -(n)\right) \Rightarrow kernel\left(alpha, beta, z, s\right) = \frac{leftNumerator\left(alpha, beta, z, n, s\right)}{(s--(n))}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel_eq_leftNumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

Gamma recurrence factors the actual kernel as leftNumerator divided by s+n throughout the closed strip away from s=-n. This supplies the factorization field of the actual Mellin-Barnes data.

**Theorem 1.9 (The literal source coefficient).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; z\neq 0 \Rightarrow \left(\forall n \in Nat,\; leftNumerator\left(alpha, beta, z, n, -(n)\right) = \frac{z^{n}}{RealGamma\left(((alpha*n)+beta)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.leftNumerator_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

At s=-n the shifted Gamma is one, Gamma(1-s) is n factorial, and the remaining finite product is (-1)^n times n factorial. Exp(n*log(-z))=(-z)^n for nonzero z. Only the factorial is cancelled; reciprocal-Gamma zeros remain in scope.

**Theorem 1.10 (The growing Gamma denominator).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall c \in Real,\; \left(0 < alpha \land \left(sin\left((\pi *c)\right)\neq 0 \land \frac{1}{2} \le (beta-(alpha*c))\right)\right) \Rightarrow \left(\forall y \in Real,\; \left\lVert kernel\left(alpha, beta, z, (c+(y*\operatorname{ComplexI}))\right) \right\rVert \le (\frac{(\frac{(2*\pi )}{\left|sin\left((\pi *c)\right)\right|}*exp\left(-((c*log\left(\left\lVert z \right\rVert\right)))\right))}{RealGamma\left((beta-(alpha*c))\right)}*exp\left(-((margin\left(alpha, z\right)*\left|y\right|))\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_line_le_recip_gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

When beta-alpha*c is at least one half, the squared reciprocal-Gamma estimate retains Gamma(beta-alpha*c) in the denominator. Reflection and the actual angular margin give this estimate without a bounded-strip replacement constant.

**Theorem 1.11 (The half-integer sine factor).**

$$\forall n \in Nat,\; \left|sin\left((\pi *leftLine\left(n\right))\right)\right| = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.abs_sin_leftLine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

Moving the line left by one changes the sine sign, so its absolute value remains one. This is used by the integral estimate and the actual contour integrability proof.

**Theorem 1.12 (The moving-line integral bound).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall n \in Nat,\; \left(0 < alpha \land \left(0 < margin\left(alpha, z\right) \land \frac{1}{2} \le (beta-(alpha*leftLine\left(n\right)))\right)\right) \Rightarrow \left\lVert integral\left((y:Real \mapsto kernel\left(alpha, beta, z, (leftLine\left(n\right)+(y*\operatorname{ComplexI}))\right))\right) \right\rVert \le (\frac{((2*\pi )*exp\left(-((leftLine\left(n\right)*log\left(\left\lVert z \right\rVert\right)))\right))}{RealGamma\left((beta-(alpha*leftLine\left(n\right)))\right)}*integral\left((y:Real \mapsto exp\left(-((margin\left(alpha, z\right)*\left|y\right|))\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_integral_leftLine_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The entire vertical integral is bounded by its retained real-Gamma radial factor times the fixed integral of exp(-margin*abs(y)). This bound is used in the literal coefficient summability argument.

**Theorem 1.13 (Both horizontal limits).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall a \in Real,\; \forall b \in Real,\; \left(0 < alpha \land \left(a \le b \land 0 < margin\left(alpha, z\right)\right)\right) \Rightarrow \left(Tendsto\left((T:Real \mapsto intervalIntegral\left((x:Real \mapsto kernel\left(alpha, beta, z, (x+(T*\operatorname{ComplexI}))\right)), a, b\right)), atTop, nhds\left(0\right)\right) \land Tendsto\left((T:Real \mapsto intervalIntegral\left((x:Real \mapsto kernel\left(alpha, beta, z, (x+(T*\operatorname{ComplexI}))\right)), a, b\right)), atBot, nhds\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.horizontal_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

On each finite real strip, the reciprocal-Gamma strip estimate and the far-horizontal sine lower bound give one polynomial-exponential majorant independent of the real coordinate. The interval integral is bounded by the strip width times that majorant. The positive angular margin forces both limits to zero.

**Definition 1.14 (The right contour sequence).**

$$\forall n \in Nat,\; rightLine\left(n\right) = (n+\frac{1}{2})$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.rightLine` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The line indexed by n has real part n plus one half.

**Definition 1.15 (The right-strip numerator).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall n \in Nat,\; \forall s \in Complex,\; rightNumerator\left(alpha, beta, z, n, s\right) = -(\frac{(((ComplexGamma\left(s\right)*\frac{1}{ComplexGamma\left((beta-(alpha*s))\right)})*exp\left((-(s)*log\left(-(z)\right))\right))*ComplexGamma\left((((1-s)+n)+1)\right))}{product\left(range\left(n\right), (j:Nat \mapsto ((1-s)+j))\right)})$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.rightNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The minus sign accounts for 1-s+n being the negative of s-(n+1). The finite product removes the earlier poles.

**Theorem 1.16 (Holomorphy on each right strip).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall n \in Nat,\; DifferentiableOn\left(Complex, (s:Complex \mapsto rightNumerator\left(alpha, beta, z, n, s\right)), preimage\left(re, Icc\left(rightLine\left(n\right), rightLine\left((n+1)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.differentiableOn_rightNumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

Both ordinary Gamma arguments have positive real part on the strip. The earlier finite factors never vanish there, and reciprocal Gamma is entire.

**Theorem 1.17 (The actual right-strip factorization).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \forall n \in Nat,\; \forall s \in Complex,\; \left(mem\left(re\left(s\right), Icc\left(rightLine\left(n\right), rightLine\left((n+1)\right)\right)\right) \land s\neq (n+1)\right) \Rightarrow kernel\left(alpha, beta, z, s\right) = \frac{rightNumerator\left(alpha, beta, z, n, s\right)}{(s-(n+1))}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel_eq_rightNumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

Gamma recurrence gives the actual kernel divided by s-(n+1), away from the single pole.

**Theorem 1.18 (The rightward reciprocal-Gamma residue).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; z\neq 0 \Rightarrow \left(\forall n \in Nat,\; rightNumerator\left(alpha, beta, z, n, (n+1)\right) = \frac{\frac{1}{z^{(n+1)}}}{RealGamma\left((beta-(alpha*(n+1)))\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.rightNumerator_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

At n+1 the factorial and sign cancel. The residue is the inverse z power times reciprocal Gamma, including its zeros.

**Theorem 1.19 (The right half-integer sine factor).**

$$\forall n \in Nat,\; \left|sin\left((\pi *rightLine\left(n\right))\right)\right| = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.abs_sin_rightLine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

Advancing by one changes the sine sign and preserves its absolute value.

**Theorem 1.20 (The actual rightward shift in dy).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall z \in Complex,\; \left(0 < alpha \land \left(z\neq 0 \land 0 < margin\left(alpha, z\right)\right)\right) \Rightarrow \left(\forall n \in Nat,\; (integral\left((y:Real \mapsto kernel\left(alpha, beta, z, (rightLine\left((n+1)\right)+(y*\operatorname{ComplexI}))\right))\right)-integral\left((y:Real \mapsto kernel\left(alpha, beta, z, (rightLine\left(n\right)+(y*\operatorname{ComplexI}))\right))\right)) = ((2*\pi )*\frac{\frac{1}{z^{(n+1)}}}{RealGamma\left((beta-(alpha*(n+1)))\right)})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.integral_right_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The right line integral minus the left line integral is two pi times the actual residue. Holomorphy, integrability and both horizontal limits are supplied by the literal kernel.

**Theorem 1.21 (The margin under positive radial scaling).**

$$\forall alpha \in Real,\; \forall r \in Real,\; \forall w \in Complex,\; 0 < r \Rightarrow margin\left(alpha, (r*w)\right) = margin\left(alpha, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.margin_pos_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

Positive real scaling preserves the principal argument of minus w.

**Theorem 1.22 (The exact radial norm factor).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall c \in Real,\; \forall y \in Real,\; \forall r \in Real,\; \forall w \in Complex,\; \left(0 < r \land w\neq 0\right) \Rightarrow \left\lVert kernel\left(alpha, beta, (r*w), (c+(y*\operatorname{ComplexI}))\right) \right\rVert = (rpow\left(r, -(c)\right)*\left\lVert kernel\left(alpha, beta, w, (c+(y*\operatorname{ComplexI}))\right) \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_kernel_pos_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The principal logarithm of r times minus w is log r plus log of minus w. Its exponential has norm r to the power minus c.

**Theorem 1.23 (The fixed-line radial integral bound).**

$$\forall alpha \in Real,\; \forall beta \in Real,\; \forall c \in Real,\; \forall w \in Complex,\; \forall r \in Real,\; \left(0 < alpha \land \left(sin\left((\pi *c)\right)\neq 0 \land \left(w\neq 0 \land \left(0 < margin\left(alpha, w\right) \land 0 < r\right)\right)\right)\right) \Rightarrow \left\lVert integral\left((y:Real \mapsto kernel\left(alpha, beta, (r*w), (c+(y*\operatorname{ComplexI}))\right))\right) \right\rVert \le (rpow\left(r, -(c)\right)*integral\left((y:Real \mapsto \left\lVert kernel\left(alpha, beta, w, (c+(y*\operatorname{ComplexI}))\right) \right\rVert)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_integral_pos_scale_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The actual integrable kernel at w supplies a constant independent of r. The vertical integral at r times w has norm at most that constant times r to the power minus c.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.abs_sin_leftLine`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.abs_sin_rightLine`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.differentiableOn_leftNumerator`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.differentiableOn_rightNumerator`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.exists_line_majorant`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.horizontal_tendsto_zero`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.integrable_line`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.integral_right_step`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel_eq_leftNumerator`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel_eq_rightNumerator`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.leftLine`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.leftNumerator`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.leftNumerator_residue`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.margin`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.margin_pos_scale`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_integral_leftLine_le`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_integral_pos_scale_le`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_kernel_pos_scale`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.norm_line_le_recip_gamma`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.rightLine`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.rightNumerator`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.rightNumerator_residue`
- Dependency: [D5/S3/Analytic/Asymptotics/BarnesResidue](BarnesResidue.md)
- Dependency: [D5/S3/Analytic/Asymptotics/BarnesSineBounds](BarnesSineBounds.md)
- Dependency: [D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds](GammaVerticalReciprocalBounds.md)
