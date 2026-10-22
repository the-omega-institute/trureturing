# MatrixGaussianPoisson

## Abstract

For every natural rank r, real positive definite A and complex b with positive real part, sum_a exp(-pi b Q_A(a)) equals sqrt(det A)^(-1) b^(-r/2) sum_k exp(-pi Q_(A^(-1))(k)/b), with a and k ranging over all integer vectors of rank r. Both primal and inverse-form term norms are summable. The power is principal. The proof uses coordinate Poisson summation, the genuine matrix Fourier integral and absolute convergence of both lattice sums. No integer-coordinate diagonalization is used, and rank zero remains in scope.

**Theorem 1.1 (Positive coordinate coercivity).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\exists t \in \mathbb{R},\; 0 < t \land \left(\forall x \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; t \cdot \operatorname{sum}\left((i:\operatorname{Fin}\left(r\right) \mapsto x(i)^{2})\right) \le \operatorname{quadratic}\left(A, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianPoisson.exists_quadratic_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank r and real positive definite matrix A on Fin r, there is a real t>0 such that t sum_i x_i^2 <= Q_A(x) for every real vector x. For nonempty coordinates Cauchy-Schwarz for A^(-1) gives the reciprocal inverse-trace constant. Empty coordinates are handled separately and require no positive inverse trace.

**Theorem 1.2 (Absolute integer-vector Gaussian convergence).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \operatorname{Summable}\left((a:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \left\lVert \operatorname{exp}\left(-\pi \cdot b \cdot (\operatorname{quadratic}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (a(i):\mathbb{R}))\right):\mathbb{C})\right) \right\rVert)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianPoisson.summable_norm_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank r, real positive definite matrix A and complex b with positive real part, the norms of exp(-pi b Q_A(a)) are summable over all integer vectors a. Applying the same theorem to A^(-1) and b^(-1) supplies the dual norm sum.

**Definition 1.3 (Continuous coordinate Gaussian).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \forall x \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \operatorname{gaussianMap}\left(A, b\right)(x) = \operatorname{exp}\left(-\pi \cdot b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C})\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianPoisson.gaussianMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous map x -> exp(-pi b Q_A(x)) is defined on real coordinate space for every real matrix A and complex b.

**Theorem 1.4 (Locally normal integer periodization).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall K \in \operatorname{Compacts}\left(\operatorname{Fin}\left(r\right) \to \mathbb{R}\right),\; \operatorname{Summable}\left((a:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \left\lVert \operatorname{restrict}\left(\operatorname{comp}\left(\operatorname{gaussianMap}\left(A, b\right), \operatorname{addRight}\left((i:\operatorname{Fin}\left(r\right) \mapsto (a(i):\mathbb{R}))\right)\right), K\right) \right\rVert)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianPoisson.locally_summable_norm_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank r, real positive definite A, complex b with positive real part and compact K in real coordinate space, the sup norms on K of the integer translates of the Gaussian form a summable family. Coordinate coercivity and (x+a)^2 >= a^2/2-x^2 give a uniform summable product majorant.

**Theorem 1.5 (General positive-matrix Gaussian Poisson identity).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\operatorname{Summable}\left((a:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \left\lVert \operatorname{exp}\left(-\pi \cdot b \cdot (\operatorname{quadratic}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (a(i):\mathbb{R}))\right):\mathbb{C})\right) \right\rVert)\right) \land \left(\operatorname{Summable}\left((k:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \left\lVert \operatorname{exp}\left(\frac{-\pi}{b} \cdot (\operatorname{quadratic}\left(A^{-1}, (i:\operatorname{Fin}\left(r\right) \mapsto (k(i):\mathbb{R}))\right):\mathbb{C})\right) \right\rVert)\right) \land \operatorname{tsum}\left((a:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \operatorname{exp}\left(-\pi \cdot b \cdot (\operatorname{quadratic}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (a(i):\mathbb{R}))\right):\mathbb{C})\right))\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot b^{\frac{-(r:\mathbb{C})}{2}} \cdot \operatorname{tsum}\left((k:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \operatorname{exp}\left(\frac{-\pi}{b} \cdot (\operatorname{quadratic}\left(A^{-1}, (i:\operatorname{Fin}\left(r\right) \mapsto (k(i):\mathbb{R}))\right):\mathbb{C})\right))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianPoisson.poisson_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank r, real positive definite A and complex b with positive real part, sum_a exp(-pi b Q_A(a)) equals sqrt(det A)^(-1) b^(-r/2) sum_k exp(-pi Q_(A^(-1))(k)/b), with a and k ranging over all integer vectors of rank r. Both primal and inverse-form term norms are summable. The power is principal. The proof uses coordinate Poisson summation, the genuine matrix Fourier integral and absolute convergence of both lattice sums. No integer-coordinate diagonalization is used, and rank zero remains in scope.

## References

- Truth anchor: `D5/S3/Fourier/MatrixGaussianPoisson.exists_quadratic_lower_bound`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianPoisson.gaussianMap`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianPoisson.locally_summable_norm_gaussian`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianPoisson.poisson_gaussian`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianPoisson.summable_norm_gaussian`
- Dependency: [D5/S3/Fourier/CoordinatePoisson](CoordinatePoisson.md)
- Dependency: [D5/S3/Fourier/MatrixGaussian](MatrixGaussian.md)
