# The integrated Poisson and signed Schur kernel

## Abstract

The actual Poisson densities and the Fourier boundary kernel satisfy normalized L1 control on the strict interior real interval, including the closed parameter edge b=1.

**Definition 1.1 (The actual disk Poisson density).**

$$\forall t : \mathbb{R}, \forall theta : \mathbb{R}, \operatorname{poissonDensity}\left(t, theta\right) = \operatorname{poissonKernel}\left(0, t, \operatorname{circleMap}\left(0, 1, theta\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.poissonDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function uses Mathlib's actual disk Poisson kernel at the real point t and actual unit-circle point circleMap(0,1,theta). The kernel is used only for |t|<1; no boundary Poisson formula is assumed.

**Definition 1.2 (The oriented Poisson integral).**

$$\forall x : \mathbb{R}, \forall theta : \mathbb{R}, \operatorname{integratedPoisson}\left(x, theta\right) = \operatorname{integral}\left(0, x, (t : \mathbb{R}) \mapsto \operatorname{poissonDensity}\left(t, theta\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.integratedPoisson` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interval integral runs from zero to x with its orientation. For |x|<1, the entire segment lies strictly inside the disk. The angle function is continuous and all integrals used in the proof exist.

**Theorem 1.3 (Normalized L1 control on the entire interior interval).**

$$\forall b : \mathbb{R}, \forall x : \mathbb{R}, 0 \le b \le 1 \land \operatorname{abs}\left(x\right) < 1 \implies \frac{1}{2\pi} \operatorname{integral}\left(0, 2\pi, (theta : \mathbb{R}) \mapsto \operatorname{abs}\left(\operatorname{integratedPoisson}\left(x, theta\right)-\operatorname{boundaryKernel}\left(b, theta\right)\right)\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.boundary_l1_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized integral of |A_x-B_b| is at most one for every |x|<1 and b in [0,1]. On nonnegative x, the Poisson lower estimate and the polynomial sum from k=1 to 5 of ((1-t)/2)^k yield A_x >= x(367/960) >= x(3067/8100). The polynomial's integral is exactly 367/960. The actual Poisson mean is one, proved by applying the Poisson formula to the constant complex function; continuous integrability on the compact time-angle rectangle justifies the swap giving mean A_x=x. The boundary kernel has mean zero and absolute value at most 3067/8100. Therefore |A_x-B_b| <= A_x-B_b+2(1-x)(3067/8100), and its mean is at most one. The identities P(-t,theta)=P(t,theta+pi) and B_b(theta+pi)=-B_b(theta), with periodic interval integration, prove the negative-x case. The value b=1 uses the proved closed-domain kernel controls. This scalar control bounds the actual primitive functional below, using its derived boundary representation.

**Theorem 1.4 (The sharp actual primitive functional on the closed interval).**

$$\forall b : \mathbb{R}, \forall x : \mathbb{R}, \forall h H : \mathbb{C} \to \mathbb{C}, \operatorname{Entire}\left(h\right) \land \operatorname{HasDerivativeEverywhere}\left(H, h\right) \land \operatorname{H}\left(0\right) = 0 \land 0 < b \le 1 \land -1 \le x \le 1 \implies \operatorname{norm}\left(\operatorname{H}\left(x\right)-\frac{1}{2b}\operatorname{integral}\left(-b, b, (t : \mathbb{R}) \mapsto \operatorname{H}\left(ti\right)\right)\right) \le \operatorname{sSup}\left(\operatorname{normImageOfClosedDisk}\left(h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.primitive_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be any entire complex-valued function and H its normalized entire primitive. For every 0<b<=1 and every real x in [-1,1], the norm of H(x) minus its normalized imaginary-segment average is at most the supremum of |h| on the original closed unit disk. The norm value set is nonempty and bounded by compactness. For |x|<1, the Poisson formula applies at every real point on the segment between zero and x. Continuous integrability on the closed time-angle rectangle justifies exchanging the integrals with their orientation for negative x. Subtracting the actual B_b representation gives the exact boundary pairing with A_x-B_b. The integral triangle inequality, the actual closed-disk norm and normalized L1 control yield the estimate. Continuity of H extends the inequality to x=-1 and x=1. The case b=1 is already included in the primitive representation. No boundary Poisson formula, coefficient restriction or hypothesis about a kernel norm is imposed.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.boundary_l1_control`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.integratedPoisson`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.poissonDensity`
- Truth anchor: `D5/S3/Analytic/Interpolation/SchurIntegratedKernel.primitive_error_bound`
- Dependency: [D5/S3/Analytic/Interpolation/SchurBoundaryKernel](SchurBoundaryKernel.md)
