# MatrixGaussian

## Abstract

For every finite coordinate type n, real positive definite A, complex b with positive real part and real frequency w, the integral of exp(-2 pi i w dot x) exp(-pi b Q_A(x)) is sqrt(det A)^(-1) b^(-card(n)/2) exp(-pi Q_(A^(-1))(w)/b). The right half-plane excludes the inverse-power branch cut.

**Definition 1.1 (Coordinate quadratic form).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \forall x \in n \to \mathbb{R},\; \operatorname{quadratic}\left(A, x\right) = \operatorname{dotProduct}\left(x, \operatorname{mulVec}\left(A, x\right)\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussian.quadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate set n and real square matrix A, quadratic A x is x dotProduct (A mulVec x), with both operations in real coordinates.

**Theorem 1.2 (Integrability with complex linear phase).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall c \in \mathbb{C},\; \forall w \in n \to \mathbb{R},\; \operatorname{Integrable}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C}) + c \cdot (\operatorname{dotProduct}\left(w, x\right):\mathbb{C})\right)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussian.integrable_gaussian_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite coordinate type n, real positive definite A, complex b with positive real part, complex c and real coordinate vector w, exp(-b Q_A(x)+c w dot x) is integrable for coordinate Lebesgue measure. The empty coordinate set is included.

**Theorem 1.3 (The coordinate Gaussian integral).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall c \in \mathbb{C},\; \forall w \in n \to \mathbb{R},\; \operatorname{integral}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C}) + c \cdot (\operatorname{dotProduct}\left(w, x\right):\mathbb{C})\right)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot \frac{\pi}{b}^{\frac{(\operatorname{card}\left(n\right):\mathbb{C})}{2}} \cdot \operatorname{exp}\left(\frac{c^{2} \cdot (\operatorname{quadratic}\left(A^{-1}, w\right):\mathbb{C})}{4 \cdot b}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussian.integral_gaussian_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite coordinate type n, real positive definite A, complex b with positive real part, complex c and real w, the coordinate Lebesgue integral of exp(-b Q_A(x)+c w dot x) is sqrt(det A)^(-1) (pi/b)^(card(n)/2) exp(c^2 Q_(A^(-1))(w)/(4b)). Complex powers use the principal branch. The change of variables is the real positive matrix square root; its determinant gives the coordinate-volume factor.

**Theorem 1.4 (The normalized matrix Fourier kernel).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall w \in n \to \mathbb{R},\; \operatorname{integral}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-2 \cdot \pi \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{dotProduct}\left(w, x\right):\mathbb{C})\right) \cdot \operatorname{exp}\left(-\pi \cdot b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C})\right)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot b^{\frac{-(\operatorname{card}\left(n\right):\mathbb{C})}{2}} \cdot \operatorname{exp}\left(\frac{-\pi}{b} \cdot (\operatorname{quadratic}\left(A^{-1}, w\right):\mathbb{C})\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussian.integral_fourier_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite coordinate type n, real positive definite A, complex b with positive real part and real frequency w, the integral of exp(-2 pi i w dot x) exp(-pi b Q_A(x)) is sqrt(det A)^(-1) b^(-card(n)/2) exp(-pi Q_(A^(-1))(w)/b). The right half-plane excludes the inverse-power branch cut.

**Definition 1.5 (Complex bilinear Gram square).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \forall z \in n \to \mathbb{C},\; \operatorname{complexQuadratic}\left(A, z\right) = \operatorname{dotProduct}\left(z, \operatorname{mulVec}\left(\operatorname{map}\left(A, ofReal\right), z\right)\right)$$

*Formalization.* `D5/S3/Fourier/MatrixGaussian.complexQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the complex bilinear extension z dot A z. It contains no complex conjugation.

**Theorem 1.6 (Independent complex-source integrability).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall z \in n \to \mathbb{C},\; \operatorname{Integrable}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C}) + \operatorname{dotProduct}\left(z, (i:n \mapsto (\operatorname{x}\left(i\right):\mathbb{C}))\right)\right)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussian.integrable_gaussian_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coordinate of z is independently complex. The proof uses Mathlib's arbitrary-coefficient Gaussian product and the existing real positive square-root change of variables. Rank zero is included.

**Theorem 1.7 (Independent complex-source Gaussian integral).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall z \in n \to \mathbb{C},\; \operatorname{integral}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-b \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C}) + \operatorname{dotProduct}\left(z, (i:n \mapsto (\operatorname{x}\left(i\right):\mathbb{C}))\right)\right)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot \frac{\pi}{b}^{\frac{(\operatorname{card}\left(n\right):\mathbb{C})}{2}} \cdot \operatorname{exp}\left(\frac{\operatorname{complexQuadratic}\left(A^{-1}, z\right)}{4 \cdot b}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussian.integral_gaussian_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral is sqrt(det A)^(-1) (pi/b)^(card(n)/2) exp(Q_(A inverse)(z)/(4b)). Coordinate volume fixes the determinant factor; the exponent uses the complex bilinear square.

**Theorem 1.8 (Independent complex-source Fourier transform).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A \in \operatorname{Matrix}\left(n, n, \mathbb{R}\right),\; \operatorname{PosDef}\left(A\right) \Rightarrow \left(\forall b \in \mathbb{C},\; 0 < \operatorname{re}\left(b\right) \Rightarrow \left(\forall z \in n \to \mathbb{C},\; \forall w \in n \to \mathbb{R},\; \operatorname{integral}\left((x:n \to \mathbb{R} \mapsto \operatorname{exp}\left(-2 \cdot \pi \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{dotProduct}\left(w, x\right):\mathbb{C})\right) \cdot \operatorname{exp}\left(-\left(\pi \cdot b\right) \cdot (\operatorname{quadratic}\left(A, x\right):\mathbb{C}) + \operatorname{dotProduct}\left(z, (i:n \mapsto (\operatorname{x}\left(i\right):\mathbb{C}))\right)\right)), \operatorname{volume}\left(n \to \mathbb{R}\right)\right) = (\operatorname{sqrt}\left(\operatorname{det}\left(A\right)\right):\mathbb{C})^{-1} \cdot b^{\frac{-(\operatorname{card}\left(n\right):\mathbb{C})}{2}} \cdot \operatorname{exp}\left(\frac{\operatorname{complexQuadratic}\left(A^{-1}, (i:n \mapsto \operatorname{z}\left(i\right) - 2 \cdot \pi \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{w}\left(i\right):\mathbb{C}))\right)}{4 \cdot \pi \cdot b}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MatrixGaussian.integral_fourier_gaussian_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual real-coordinate Fourier integral shifts z to z-2 pi i w inside the inverse bilinear quadratic form. The principal complex power is b^(-card(n)/2); the right half-plane supplies its branch condition.

## References

- Truth anchor: `D5/S3/Fourier/MatrixGaussian.complexQuadratic`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integrable_gaussian_linear`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integrable_gaussian_source`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integral_fourier_gaussian`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integral_fourier_gaussian_source`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integral_gaussian_linear`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integral_gaussian_source`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.quadratic`
