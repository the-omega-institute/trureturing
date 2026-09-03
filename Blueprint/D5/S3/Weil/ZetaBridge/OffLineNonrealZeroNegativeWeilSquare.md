# Off-Line Nonreal Zero Negative Weil Square

## Abstract

An off-line nonreal zero admits a powered even separator whose full Weil-square zero sum has strictly negative real part.

**Theorem 1.1 (An off-line nonreal zero yields a negative full Weil-square zero sum).**

$$\forall Z \in ZeroData, n \in \mathbb{N},\; \left(\Re (\operatorname{zero}\left(Z, n\right)) \ne criticalAbscissa \land \operatorname{Im} (\operatorname{zero}\left(Z, n\right)) \ne 0\right) \Rightarrow \left(\exists g \in WeilTestFunction, hZero \in \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right),\; \Re (\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), hZero\right)) < 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.offLineNonrealZero_yields_negative_weil_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite even interpolation first prescribes a unit peak and an exception killer. Convolution powering preserves the target values while the frozen closed-strip decay makes the complement geometrically small.

Frozen zeta-zero absolute summability identifies every symmetric zero-sum witness with the ordinary sum. Splitting that sum into the four-point orbit and its complement leaves the prescribed negative orbit larger in magnitude than the tail.

The explicit nonzero imaginary-part hypothesis is the M3-d input. The theorem is conditional on that input and asserts no implication from O-6 to the Riemann hypothesis.

**Theorem 1.2 (A unit peak and finite-exception killer exist).**

$$\forall Z \in ZeroData, n \in \mathbb{N},\; \left(\Re (\operatorname{zero}\left(Z, n\right)) \ne criticalAbscissa \land \operatorname{Im} (\operatorname{zero}\left(Z, n\right)) \ne 0\right) \Rightarrow \left(\exists b \in WeilTestFunction, k \in WeilTestFunction, E \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\left(\left(\left(\left(\left(\left(\left(\forall j \in \mathbb{N},\; j \in E \Leftrightarrow \operatorname{reflection}\left(Z, j\right) \in E\right) \land \left(\forall j \in \mathbb{N},\; j \in E \Leftrightarrow \operatorname{conjugation}\left(Z, j\right) \in E\right)\right) \land \operatorname{zeroOrbit}\left(Z, n\right) \subseteq E\right) \land \operatorname{fourierLaplace}\left(b, \operatorname{gamma}\left(Z, n\right)\right) = 1\right) \land \operatorname{fourierLaplace}\left(b, \operatorname{conj}\left(\operatorname{gamma}\left(Z, n\right)\right)\right) = 1\right) \land \operatorname{fourierLaplace}\left(k, \operatorname{gamma}\left(Z, n\right)\right) = 1\right) \land \operatorname{fourierLaplace}\left(k, \operatorname{conj}\left(\operatorname{gamma}\left(Z, n\right)\right)\right) = -1\right) \land \left(\forall j \in \mathbb{N},\; \left(\neg j \in E\right) \Rightarrow \left(\left\lVert \operatorname{fourierLaplace}\left(b, \operatorname{gamma}\left(Z, j\right)\right) \right\rVert \le \frac{1}{2} \land \left\lVert \operatorname{fourierLaplace}\left(b, \operatorname{conj}\left(\operatorname{gamma}\left(Z, j\right)\right)\right) \right\rVert \le \frac{1}{2}\right)\right)\right) \land \left(\forall j \in \mathbb{N},\; \left(j \in E \land \left(\neg j \in \operatorname{zeroOrbit}\left(Z, n\right)\right)\right) \Rightarrow \left(\operatorname{fourierLaplace}\left(k, \operatorname{gamma}\left(Z, j\right)\right) = 0 \land \operatorname{fourierLaplace}\left(k, \operatorname{conj}\left(\operatorname{gamma}\left(Z, j\right)\right)\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.exists_peak_and_finite_exception_killer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exceptional set is a sufficiently large symmetric spectral ball. Closed-strip decay bounds the peak function outside it, while finite even interpolation makes the killer vanish at every exceptional frequency away from the target orbit and prescribes opposite values on the target conjugate pair.

**Theorem 1.3 (The powered complement obeys Burnol's geometric tail bound).**

$$\forall Z \in ZeroData, n \in \mathbb{N}, b \in WeilTestFunction, k \in WeilTestFunction, E \in \operatorname{Finset}\left(\mathbb{N}\right), N \in \mathbb{N},\; \left(\left(\forall i \in \mathbb{N},\; \left(\neg i \in E\right) \Rightarrow \left(\left\lVert \operatorname{fourierLaplace}\left(b, \operatorname{gamma}\left(Z, i\right)\right) \right\rVert \le \frac{1}{2} \land \left\lVert \operatorname{fourierLaplace}\left(b, \operatorname{conj}\left(\operatorname{gamma}\left(Z, i\right)\right)\right) \right\rVert \le \frac{1}{2}\right)\right) \land \left(\forall i \in \mathbb{N},\; \left(i \in E \land \left(\neg i \in \operatorname{zeroOrbit}\left(Z, n\right)\right)\right) \Rightarrow \left(\operatorname{fourierLaplace}\left(k, \operatorname{gamma}\left(Z, i\right)\right) = 0 \land \operatorname{fourierLaplace}\left(k, \operatorname{conj}\left(\operatorname{gamma}\left(Z, i\right)\right)\right) = 0\right)\right)\right) \Rightarrow \left(\operatorname{Summable}\left((j: \left\{\neg j \in \operatorname{zeroOrbit}\left(Z, n\right) \mid j \in \mathbb{N}\right\} \mapsto \operatorname{zeroSummand}\left(Z, \operatorname{convolutionSquare}\left(\operatorname{convolve}\left(\operatorname{convolutionSuccPower}\left(b, N\right), k\right)\right), \operatorname{val}\left(j\right)\right))\right) \land \left\lVert \sum_{j \in \left\{\neg j \in \operatorname{zeroOrbit}\left(Z, n\right) \mid j \in \mathbb{N}\right\}} \operatorname{zeroSummand}\left(Z, \operatorname{convolutionSquare}\left(\operatorname{convolve}\left(\operatorname{convolutionSuccPower}\left(b, N\right), k\right)\right), \operatorname{val}\left(j\right)\right) \right\rVert \le (\frac{1}{4})^{N + 1} \cdot \sum_{j \in \mathbb{N}} \left\lVert \operatorname{zeroSummand}\left(Z, \operatorname{convolutionSquare}\left(k\right), j\right) \right\rVert\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.burnol_power_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Outside the target orbit, exceptional indices vanish by the killer and all remaining indices acquire a factor at most one quarter at each convolution-power step. Absolute zeta-zero summability supplies the full majorant and permits summation over the subtype complement.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.burnol_power_tail_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.exists_peak_and_finite_exception_killer`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.offLineNonrealZero_yields_negative_weil_square`
- Dependency: [D5/S3/Fourier/ConvolutionPowerAmplification](../../Fourier/ConvolutionPowerAmplification.md)
- Dependency: [D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation](../TestFunctions/EvenTestFunctionFiniteInterpolation.md)
- Dependency: [D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay](../TestFunctions/FourierLaplaceClosedStripDecay.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit](PrescribedPairNegativeOrbit.md)
- Dependency: [D5/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable](SymmetricConvergentOfZetaSummable.md)
