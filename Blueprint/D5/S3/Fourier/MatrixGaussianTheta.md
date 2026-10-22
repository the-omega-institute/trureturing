# MatrixGaussianTheta

## Abstract

For every natural rank r, real positive definite A and complex tau with positive imaginary part, theta A (-1/tau) equals (-i tau)^(r/2) divided by sqrt(det A), times theta (A^(-1)) tau. The power is principal and rank zero is included.

**Definition 1.1 (Real matrix theta series).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall tau \in \mathbb{C},\; \operatorname{theta}\left(A, tau\right) = \operatorname{tsum}\left((a:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \operatorname{exp}\left(\pi \cdot \operatorname{Complex}.\operatorname{I} \cdot tau \cdot (\operatorname{quadratic}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (a(i):\mathbb{R}))\right):\mathbb{C})\right))\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianTheta.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural rank r, real coordinate matrix A and complex tau, theta A tau is the sum over all integer vectors a of exp(pi i tau Q_A(a)).

**Theorem 1.2 (Upper half-plane norm convergence).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall tau \in \mathbb{C},\; 0 < \operatorname{im}\left(tau\right) \Rightarrow \operatorname{Summable}\left((a:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \left\lVert \operatorname{exp}\left(\pi \cdot \operatorname{Complex}.\operatorname{I} \cdot tau \cdot (\operatorname{quadratic}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (a(i):\mathbb{R}))\right):\mathbb{C})\right) \right\rVert)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianTheta.summable_norm_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank r, real positive definite A and complex tau with positive imaginary part, the norms of the terms defining theta A tau are summable.

**Theorem 1.3 (Inverse-matrix theta inversion).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall tau \in \mathbb{C},\; 0 < \operatorname{im}\left(tau\right) \Rightarrow \operatorname{theta}\left(A, \frac{-1}{tau}\right) = \left(-\operatorname{Complex}.\operatorname{I} \cdot tau\right)^{\frac{(r:\mathbb{C})}{2}} \cdot (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot \operatorname{theta}\left(A^{-1}, tau\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianTheta.theta_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank r, real positive definite A and complex tau with positive imaginary part, theta A (-1/tau) equals (-i tau)^(r/2) divided by sqrt(det A), times theta (A^(-1)) tau. The power is principal and rank zero is included.

## References

- Truth anchor: `D5/S3/Fourier/MatrixGaussianTheta.summable_norm_theta`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianTheta.theta`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianTheta.theta_inversion`
- Dependency: [D5/S3/Fourier/MatrixGaussianPoisson](MatrixGaussianPoisson.md)
