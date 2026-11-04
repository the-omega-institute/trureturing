# The boundary kernel of the imaginary-axis primitive average

## Abstract

The actual Fourier kernel has a uniformly convergent series, reflection symmetry and the required sign on the full closed parameter range.

**Definition 1.1 (The actual Fourier term).**

$$\forall b : \mathbb{R}, \forall t : \mathbb{R}, \forall j : \mathbb{N}, \operatorname{boundaryTerm}\left(b, t, j\right) = \frac{2(-1)^{j+1}b^{2j+2}}{(2j+2)(2j+3)}\operatorname{cos}\left((2j+1)t\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundaryTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The term is 2(-1)^(j+1)b^(2j+2) cos((2j+1)t)/((2j+2)(2j+3)). These are the coefficients of B_b in the source; no sign or size contract is postulated.

**Definition 1.2 (The source Fourier series).**

$$\forall b : \mathbb{R}, \forall t : \mathbb{R}, \operatorname{boundaryKernel}\left(b, t\right) = \operatorname{tsum}\left(\operatorname{boundaryTerm}\left(b, t\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundaryKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel is the real tsum of its actual terms. A summable inverse-square majorant controls the series uniformly on b in [0,1] and all real angles.

**Theorem 1.3 (Uniform convergence, reflection and sign including b=1).**

$$\forall b : \mathbb{R}, \forall t : \mathbb{R}, 0 \le b \le 1 \implies \operatorname{Continuous}\left(\operatorname{boundaryKernel}\left(b\right)\right) \land \operatorname{boundaryKernel}\left(b, \operatorname{pi}\left(\right)-t\right) = -\operatorname{boundaryKernel}\left(b, t\right) \land \operatorname{cos}\left(t\right)\operatorname{boundaryKernel}\left(b, t\right) \le 0 \land \operatorname{UniformConvergenceOn}\left(\operatorname{partialSumsOfBoundaryTerms}\left(\right), \operatorname{boundaryKernel}\left(\right), \operatorname{closedParameterStrip}\left(\right)\right) \land \operatorname{ContinuousOn}\left(\operatorname{boundaryKernelOfPair}\left(\right), \operatorname{closedParameterStrip}\left(\right)\right) \land \operatorname{integral}\left(0, 2\pi, \operatorname{boundaryKernel}\left(b\right)\right) = 0 \land \operatorname{abs}\left(\operatorname{boundaryKernel}\left(b, t\right)\right) \le \frac{3067}{8100} \land \frac{3067}{8100} < \frac{19}{50}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundary_kernel_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b in [0,1], the angle function is continuous, B_b(pi-t)=-B_b(t), and cos(t) B_b(t) is nonpositive. Partial sums converge uniformly on the full strip [0,1] times the real line. For b<1, the proof integrates the actual geometric cosine series, obtaining B_b(t)=-2b squared cos(t) times the integral from zero to one of u(1-u)(1+b squared u squared)/((1-b squared u squared) squared+4b squared u squared cos(t) squared). The integrand is nonnegative. Continuity in b extends the sign to b=1, including cos(t)=0. The joint parameter-angle function is continuous on the full strip. Termwise cosine integration gives zero mean. The rational size estimate is |B_b(t)| <= 3067/8100 < 19/50. After y=bu the nonnegative integral is bounded by the integral of (1-y)q(y,c), c=|cos(t)|. On [0,1/3] this is at most 2y(1-y)(1-9y squared/10), whose integral is 667/8100. On [1/3,1] it is at most 3/8+y/8-3(y-1/3)(1-y)/16, whose integral is 8/27. Continuity includes b=1. The rational bound is sufficient for the integrated-kernel estimate. It does not assert the separate logarithm-arctangent constant C.

**Theorem 1.4 (The normalized entire primitive representation).**

$$\forall h : \mathbb{C} \to \mathbb{C}, \forall H : \mathbb{C} \to \mathbb{C}, \forall b : \mathbb{R}, \operatorname{Entire}\left(h\right) \land \operatorname{HasDerivativeEverywhere}\left(H, h\right) \land \operatorname{H}\left(0\right) = 0 \land 0 < b \le 1 \implies \frac{1}{2b}\operatorname{integral}\left(-b, b, (t : \mathbb{R}) \mapsto \operatorname{H}\left(it\right)\right) = \frac{1}{2\pi}\operatorname{integral}\left(0, 2\pi, (t : \mathbb{R}) \mapsto \operatorname{h}\left(\operatorname{circleMap}\left(0, 1, t\right)\right)\operatorname{boundaryKernel}\left(b, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundary_primitive_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be any entire complex-valued function and let H have complex derivative h everywhere and H(0)=0. Then the normalized integral of H(it) from -b to b is the circle pairing of h with the actual real Fourier kernel, for every 0<b<=1. The primitive is entire because it is complex differentiable everywhere; existence of a normalized entire primitive follows from the exact primitive theorem on the complex plane. For 0<b<1, the Cauchy mean formula gives the average of h(z)/(z-w). Applying it at w=ir and w=-ir, and conjugating only the rational kernel z/(1+r squared z squared) on the unit circle, gives its real-part pairing. Continuity and compact product integrability justify exchanging the time and angle integrals. The fundamental theorem of calculus applied to (1-t)(H(ibt)+H(-ibt)) identifies the resulting weighted integral. Real changes of variables give the displayed vertical-segment average. Joint continuity of the actual kernel and compact parameter integrals extend the identity to b=1. No conjugation identity for h or H is assumed, and all coefficients remain arbitrary complex numbers.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundaryKernel`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundaryTerm`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundary_kernel_control`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurBoundaryKernel.boundary_primitive_representation`
