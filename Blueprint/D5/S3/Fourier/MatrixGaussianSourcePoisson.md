# MatrixGaussianSourcePoisson

## Abstract

Positive matrix Gaussians with independent complex coordinate sources have normal lattice convergence and a sourceful Poisson formula in coordinate volume.

**Definition 1.1 (Gaussian with independent complex sources).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \forall x \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \operatorname{sourceGaussianMap}\left(A, b, z, x\right) = \operatorname{exp}\left(-\pi \cdot b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C}) + \operatorname{dotProduct}\left(z, \operatorname{castComplexVector}\left(x\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianSourcePoisson.sourceGaussianMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite rank r, real Gram matrix A, complex b and complex coordinate vector z, this is the continuous real-coordinate function exp(-pi b Q_A(x)+sum_i z_i x_i).

**Theorem 1.2 (Uniform source absorption).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall t \in \mathbb{R},\; 0 < t \Rightarrow \left(\operatorname{quadraticLowerBound}\left(A, t\right) \Rightarrow \left(\forall R \in \mathbb{R},\; \forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \operatorname{realSourceBound}\left(z, R\right) \Rightarrow \left(\forall x \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \left\lVert \operatorname{sourceGaussianMap}\left(A, b, z, x\right) \right\rVert \le \operatorname{exp}\left(\frac{r \cdot R^{2}}{2 \cdot \pi \cdot \operatorname{re}\left(b\right) \cdot t \cdot 1}\right) \cdot \left\lVert \operatorname{gaussianMap}\left(A, \frac{b}{2}, x\right) \right\rVert\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourcePoisson.source_gaussian_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Re b>0 and t>0 with t sum_i x_i squared bounded by Q_A(x) for every real x. If every real part of z_i has absolute value at most R, then the norm is bounded by exp(r R squared/(2 pi Re(b) t)) times the zero-source Gaussian with parameter b/2. The bound holds at every real point and includes rank zero.

**Theorem 1.3 (Uniform absorption of every finite polynomial order).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall t \in \mathbb{R},\; 0 < t \Rightarrow \left(\operatorname{quadraticLowerBound}\left(A, t\right) \Rightarrow \left(\forall R \in \mathbb{R},\; \forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \operatorname{realSourceBound}\left(z, R\right) \Rightarrow \left(\forall k \in N,\; \forall x \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \left\lVert x \right\rVert^{k} \cdot \left\lVert \operatorname{sourceGaussianMap}\left(A, b, z, x\right) \right\rVert \le \operatorname{factorial}\left(k\right) \cdot \operatorname{exp}\left(\frac{r \cdot \left(R + 1\right)^{2}}{2 \cdot \pi \cdot \operatorname{re}\left(b\right) \cdot t \cdot 1}\right) \cdot \left\lVert \operatorname{gaussianMap}\left(A, \frac{b}{2}, x\right) \right\rVert\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourcePoisson.polynomial_source_gaussian_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, the additional coordinate sup-norm weight norm(x)^k is absorbed by k! exp(r (R+1) squared/(2 pi Re(b) t)) times the same Gaussian with parameter b/2. The proof uses the exponential-series factorial bound and a real sign shift in each source coordinate. No source summability or derivative-extraction hypothesis is assumed.

**Theorem 1.4 (Absolute sourceful lattice convergence).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \operatorname{Summable}\left((a:\operatorname{Fin}\left(r\right) \to Z \mapsto \left\lVert \operatorname{sourceGaussianMap}\left(A, b, z, \operatorname{castRealVector}\left(a\right)\right) \right\rVert)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourcePoisson.summable_norm_source_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive definiteness supplies the lower bound t; the resulting half-parameter Gaussian is genuinely summable on every integer vector, including the zero-dimensional lattice.

**Theorem 1.5 (Normal convergence of integer periodizations).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \forall K \in \operatorname{Compacts}\left(\operatorname{Fin}\left(r\right) \to \mathbb{R}\right),\; \operatorname{Summable}\left((a:\operatorname{Fin}\left(r\right) \to Z \mapsto \left\lVert \operatorname{restrict}\left(\operatorname{translate}\left(\operatorname{sourceGaussianMap}\left(A, b, z\right), \operatorname{castRealVector}\left(a\right)\right), K\right) \right\rVert)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourcePoisson.locally_summable_norm_source_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed independent complex source, the compact sup norms of all integer translates are summable. This is the actual normal-convergence hypothesis consumed by CoordinatePoisson.tsum_eq_tsum_integral.

**Definition 1.6 (Lattice summand as a source function).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \forall a \in \operatorname{Fin}\left(r\right) \to Z,\; \forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \operatorname{latticeSourceMap}\left(A, b, a, z\right) = \operatorname{sourceGaussianMap}\left(A, b, z, \operatorname{castRealVector}\left(a\right)\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianSourcePoisson.latticeSourceMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each integer-vector summand is a continuous function on the whole complex source space.

**Definition 1.7 (Polynomially weighted source function).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \forall k \in N,\; \forall a \in \operatorname{Fin}\left(r\right) \to Z,\; \forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \operatorname{weightedLatticeSourceMap}\left(A, b, k, a, z\right) = (\left\lVert \operatorname{castRealVector}\left(a\right) \right\rVert^{k}:\mathbb{C}) \cdot \operatorname{sourceGaussianMap}\left(A, b, z, \operatorname{castRealVector}\left(a\right)\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussianSourcePoisson.weightedLatticeSourceMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is the kth power of the sup norm of the real integer coordinate vector.

**Theorem 1.8 (Compact-uniform convergence for all fixed polynomial degrees).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall k \in N,\; \forall K \in \operatorname{Compacts}\left(\operatorname{Fin}\left(r\right) \to \mathbb{C}\right),\; \operatorname{Summable}\left((a:\operatorname{Fin}\left(r\right) \to Z \mapsto \left\lVert \operatorname{restrict}\left(\operatorname{weightedLatticeSourceMap}\left(A, b, k, a\right), K\right) \right\rVert)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourcePoisson.locally_summable_norm_polynomial_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and every compact subset of the full complex source space, the sup norms of the weighted lattice summands are summable. This supplies polynomial Gaussian majorants. A theorem exchanging arbitrary finite source derivatives with the sum is a separate obligation.

**Theorem 1.9 (The inverse-Gram Fourier Gaussian with source).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \forall w \in \operatorname{Fin}\left(r\right) \to \mathbb{R},\; \operatorname{integral}\left((x:\operatorname{Fin}\left(r\right) \to \mathbb{R} \mapsto \operatorname{exp}\left(-2 \cdot \pi \cdot i \cdot (\operatorname{dotProduct}\left(w, x\right):\mathbb{C})\right) \cdot \operatorname{sourceGaussianMap}\left(A, b, z, x\right))\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot b^{\frac{-(r:\mathbb{C})}{2}} \cdot \operatorname{exp}\left(\frac{\operatorname{complexQuadratic}\left(A^{-1}, z\right)}{4 \cdot \pi \cdot b}\right) \cdot \operatorname{sourceGaussianMap}\left(A^{-1}, b^{-1}, \frac{-i \cdot \operatorname{mulVec}\left(\operatorname{mapOfReal}\left(A^{-1}\right), z\right)}{b}, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourcePoisson.integral_fourier_source_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fourier transform equals the determinant and principal-power factor, times exp(Q_(A inverse)(z)/(4 pi b)), times the inverse-Gram Gaussian at b inverse with source -i A inverse z/b. The source square is bilinear, without conjugation.

**Theorem 1.10 (Sourceful positive-matrix Poisson summation).**

$$\forall r \in N,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right),\; \forall b \in \mathbb{C},\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall z \in \operatorname{Fin}\left(r\right) \to \mathbb{C},\; \operatorname{tsum}\left((a:\operatorname{Fin}\left(r\right) \to Z \mapsto \operatorname{sourceGaussianMap}\left(A, b, z, \operatorname{castRealVector}\left(a\right)\right))\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot b^{\frac{-(r:\mathbb{C})}{2}} \cdot \operatorname{exp}\left(\frac{\operatorname{complexQuadratic}\left(A^{-1}, z\right)}{4 \cdot \pi \cdot b}\right) \cdot \operatorname{tsum}\left((k:\operatorname{Fin}\left(r\right) \to Z \mapsto \operatorname{sourceGaussianMap}\left(A^{-1}, b^{-1}, \frac{-i \cdot \operatorname{mulVec}\left(\operatorname{mapOfReal}\left(A^{-1}\right), z\right)}{b}, \operatorname{castRealVector}\left(k\right)\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussianSourcePoisson.poisson_gaussian_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the actual coordinate Fourier periodization engine. Positive definiteness proves the input integrability, the compact normal convergence and dual lattice summability. The conclusion has no Poisson, covariance or convergence certificate as a hypothesis.

This general analytic supplier does not by itself identify the original mod-two charge cosets, their integral-unimodular dual reindexing, or the original fourierSign multiplier. It does not assert the original coset S/T laws, fullK, Jacobi, a VOA/CFT construction, BRST/string or AdS/CFT. The overarching original goal remains active.

## References

- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.integral_fourier_source_gaussian`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.latticeSourceMap`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.locally_summable_norm_polynomial_source`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.locally_summable_norm_source_gaussian`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.poisson_gaussian_source`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.polynomial_source_gaussian_bound`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.sourceGaussianMap`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.source_gaussian_bound`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.summable_norm_source_gaussian`
- Truth anchor: `D5/S3/Fourier/MatrixGaussianSourcePoisson.weightedLatticeSourceMap`
- Dependency: [D5/S3/Fourier/MatrixGaussianPoisson](MatrixGaussianPoisson.md)
