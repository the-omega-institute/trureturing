# Finite Interpolation by Even Test Functions

## Abstract

Even Weil test functions interpolate finite data at sign-separated complex nodes.

**Theorem 1.1 (Even Fourier-Laplace interpolation at sign-separated nodes).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{Complex}\left(\right)\right),\; \left(\forall z \in \operatorname{Complex}\left(\right), w \in \operatorname{Complex}\left(\right),\; z \in S \Rightarrow \left(w \in S \Rightarrow \left(z \ne w \Rightarrow z \ne -w\right)\right)\right) \Rightarrow \left(\forall a \in S \to \operatorname{Complex}\left(\right),\; \exists g \in \operatorname{WeilTestFunction}\left(\right),\; \forall z \in S,\; \operatorname{fourierLaplace}\left(g, z\right) = a\left(z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation.even_weilTestFunction_finite_interpolation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sign separation makes squaring injective on the finite node set. A scaled even compactly supported smooth seed has nonzero transform at every node, and Lagrange interpolation in the squared nodes supplies an even polynomial differential operator with the prescribed values.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation.even_weilTestFunction_finite_interpolation`
- Dependency: [D5/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation](FinitePaleyWienerInterpolation.md)
