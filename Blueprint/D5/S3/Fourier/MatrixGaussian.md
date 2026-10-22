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

## References

- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integrable_gaussian_linear`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integral_fourier_gaussian`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.integral_gaussian_linear`
- Truth anchor: `D5/S3/Fourier/MatrixGaussian.quadratic`
