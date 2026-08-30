# Finite Paley-Wiener Interpolation

## Abstract

Finite conjugation-compatible data admit an exact compact smooth Hermitian Fourier-Laplace interpolant.

**Theorem 1.1 (Finite exact Paley-Wiener interpolation).**

$$\forall M \in \operatorname{Natural}\left(\right), z \in \operatorname{Fin}\left(M\right) \to \operatorname{Complex}\left(\right), r \in \operatorname{Fin}\left(M\right) \to \operatorname{Complex}\left(\right), conjIndex \in \operatorname{Fin}\left(M\right) \to \operatorname{Fin}\left(M\right),\; \left(\left(\operatorname{Injective}\left(z\right) \land \left(\forall j \in \operatorname{Fin}\left(M\right),\; z\left(conjIndex\left(j\right)\right) = \operatorname{conj}\left(z\left(j\right)\right)\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(M\right),\; r\left(conjIndex\left(j\right)\right) = \operatorname{conj}\left(r\left(j\right)\right)\right)\right) \Rightarrow \left(\exists L \in \operatorname{Real}\left(\right), psi \in \operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right), P \in \operatorname{Polynomial}\left(\operatorname{Complex}\left(\right)\right), f \in \operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right),\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(0 < L \land \operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), psi\right)\right) \land \operatorname{HasCompactSupport}\left(psi\right)\right) \land \operatorname{tsupport}\left(psi\right) \subseteq \operatorname{Ioo}\left(-L, L\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(M\right),\; \operatorname{fourierLaplace}\left(psi, z\left(j\right)\right) \ne 0\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(M\right),\; \operatorname{eval}\left(P, z\left(j\right)\right) = \frac{r\left(j\right)}{\operatorname{fourierLaplace}\left(psi, z\left(j\right)\right)}\right)\right) \land f = (x: \operatorname{Real}\left(\right) \mapsto \operatorname{sum}\left(k, \operatorname{support}\left(P\right), \operatorname{coeff}\left(P, k\right) \cdot \operatorname{pow}\left(-\operatorname{I}\left(\right), k\right) \cdot \operatorname{iterate}\left(deriv, k, psi\right)\left(x\right)\right))\right) \land \operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), f\right)\right) \land \operatorname{HasCompactSupport}\left(f\right)\right) \land \operatorname{tsupport}\left(f\right) \subseteq \operatorname{Ioo}\left(-L, L\right)\right) \land \left(\forall x \in \operatorname{Real}\left(\right),\; f\left(-x\right) = \operatorname{conj}\left(f\left(x\right)\right)\right)\right) \land \left(\forall w \in \operatorname{Complex}\left(\right),\; \operatorname{fourierLaplace}\left(f, w\right) = \operatorname{eval}\left(P, w\right) \cdot \operatorname{fourierLaplace}\left(psi, w\right)\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(M\right),\; \operatorname{fourierLaplace}\left(f, z\left(j\right)\right) = r\left(j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation.finite_exact_paley_wiener_interpolation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized compact bump is dilated until its Fourier-Laplace transform is nonzero at every prescribed node. Lagrange interpolation then constructs the polynomial differential multiplier, and integration by parts proves its public transform factorization.

Under the source's frozen exp(-i z x) convention, integration by parts sends partial_x to i z, so its printed P(i partial_x) psi yields P(-z); the public witness uses P(-i partial_x) to realize the stated P(z) factorization.

Conjugation-compatible nodes and values make the coefficientwise conjugation average of the Lagrange polynomial coefficient-real. Applied to the Hermitian seed, its polynomial differential construction is itself Hermitian, so the same final test function has the differential definition and global transform factorization.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation.finite_exact_paley_wiener_interpolation`
