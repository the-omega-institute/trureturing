# MatrixGaussianSecondMoment

## Abstract

Quadratic current weights have absolutely convergent Gaussian lattice sums. Their coordinate Fourier transform yields inverse-matrix second-moment inversion with the principal complex power and a positive metric correction.

**Theorem 1.1 (Quadratic-weight Fourier integration).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall u \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall w \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \operatorname{integral}\left((x:\operatorname{Fin}\left(r\right) \to \mathbb{R} \mapsto \operatorname{exp}\left(-2 \cdot \pi \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{dotProduct}\left(w, x\right):\mathbb{C})\right) \cdot (\operatorname{dotProduct}\left(u, \operatorname{mulVec}\left(A, x\right)\right):\mathbb{C}) \cdot (\operatorname{dotProduct}\left(v, \operatorname{mulVec}\left(A, x\right)\right):\mathbb{C}) \cdot \operatorname{exp}\left(-\pi \cdot b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C})\right))\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot b^{\frac{-(r:\mathbb{C})}{2}} \cdot \left(\frac{(\operatorname{dotProduct}\left(u, \operatorname{mulVec}\left(A, v\right)\right):\mathbb{C})}{2 \cdot \pi \cdot b} - \frac{(\operatorname{dotProduct}\left(u, w\right):\mathbb{C}) \cdot (\operatorname{dotProduct}\left(v, w\right):\mathbb{C})}{b^{2}}\right) \cdot \operatorname{exp}\left(\frac{-\pi}{b} \cdot (\operatorname{quadratic}\left(A^{-1}, w\right):\mathbb{C})\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSecondMoment.integral_fourier_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite rank, real positive definite Gram matrix A, complex b with positive real part, and real vectors u, v and w, the Fourier transform of B_A(u,x) B_A(v,x) exp(-pi b Q_A(x)) equals the determinant and principal-power factor times [B_A(u,v)/(2 pi b) - (u dot w)(v dot w)/b squared] exp(-pi Q_(A inverse)(w)/b). Real frequency differentiation is justified by integrable Gaussian majorants.

**Definition 1.2 (Integer-coordinate current weight).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall u \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall tau \in \mathbb{C},\; \forall n \in \operatorname{Fin}\left(r\right) \to \mathbb{Z},\; \operatorname{momentTerm}\left(A, u, v, tau, n\right) = (\operatorname{dotProduct}\left(u, \operatorname{mulVec}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (n(i):\mathbb{R}))\right)\right):\mathbb{C}) \cdot (\operatorname{dotProduct}\left(v, \operatorname{mulVec}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (n(i):\mathbb{R}))\right)\right):\mathbb{C}) \cdot \operatorname{exp}\left(\pi \cdot \operatorname{Complex}.\operatorname{I} \cdot tau \cdot (\operatorname{quadratic}\left(A, (i:\operatorname{Fin}\left(r\right) \mapsto (n(i):\mathbb{R}))\right):\mathbb{C})\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianSecondMoment.momentTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weights are bilinear pairings with the original Gram matrix. No integrality or unimodularity condition is imposed on that matrix.

**Definition 1.3 (Second-moment theta series).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall u \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall tau \in \mathbb{C},\; \operatorname{secondMoment}\left(A, u, v, tau\right) = \operatorname{tsum}\left((n:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \operatorname{momentTerm}\left(A, u, v, tau, n\right))\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianSecondMoment.secondMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series sums the two current weights over the full integer-coordinate lattice.

**Theorem 1.4 (Principal-branch second-moment inversion).**

$$\forall r \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall u \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \forall tau \in \mathbb{C},\; 0 < \operatorname{im}\left(tau\right) \Rightarrow \left(\operatorname{Summable}\left((n:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \left\lVert \operatorname{momentTerm}\left(A, u, v, \frac{-1}{tau}, n\right) \right\rVert)\right) \land \operatorname{HasSum}\left((n:\operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \operatorname{momentTerm}\left(A, u, v, \frac{-1}{tau}, n\right)), \frac{\left(-\operatorname{Complex}.\operatorname{I} \cdot tau\right)^{\frac{(r:\mathbb{C})}{2}}}{(\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})} \cdot \left(tau^{2} \cdot \operatorname{secondMoment}\left(A^{-1}, \operatorname{mulVec}\left(A, u\right), \operatorname{mulVec}\left(A, v\right), tau\right) + \frac{tau}{2 \cdot \pi \cdot \operatorname{Complex}.\operatorname{I}} \cdot (\operatorname{dotProduct}\left(u, \operatorname{mulVec}\left(A, v\right)\right):\mathbb{C}) \cdot \operatorname{theta}\left(A^{-1}, tau\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSecondMoment.second_moment_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive imaginary part of tau, the inverted series is absolutely summable and has the displayed sum. The dual Gram matrix is A inverse and its polarization vectors are A u and A v. The metric correction has coefficient tau/(2 pi i). Rank zero and zero polarizations are included. This is an analytic lattice identity; it does not assert modular invariance of the same matrix or a conformal-field trace evaluation.

Writing A as the real Gram matrix of a positive lattice and taking u and v to be coordinate unit vectors identifies the weights with the two lattice-current charges. On the dual side the transported polarizations give the literal coordinate product k_i k_j. The covariance is the original Gram entry A_ij. This correspondence supplies a matrix-moment ingredient for current identities; the operator trace, annular continuation and full modular current theorem require their own proofs.

The unweighted coordinate Fourier transform, Gaussian convergence, coordinate Poisson summation and theta principal-branch algebra are reused from MatrixGaussian, MatrixGaussianPoisson, CoordinatePoisson and MatrixGaussianTheta. The polynomial calculation is a synthesis of those suppliers with dominated differentiation; no claim of a new classical analytic identity is made.

## References

- Truth anchor: `D5/S3/Fourier/MatrixGaussianSecondMoment.integral_fourier_second_moment`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSecondMoment.momentTerm`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSecondMoment.secondMoment`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSecondMoment.second_moment_inversion`
- Dependency: [D5/S3/Fourier/MatrixGaussianTheta](MatrixGaussianTheta.md)
