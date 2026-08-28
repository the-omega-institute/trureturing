# Fixed-Scale Weil Quadratic Form

## Abstract

The fixed-scale Weil zero-side form is the completed Fourier multiplier form plus its rank-one pole energy, with an equivalent positivity test.

**Theorem 1.1 (The fixed-scale Weil form and its positivity test).**

$$\forall Z: \operatorname{ZeroData}, f\in \mathcal{W}, L\in \mathbb{R}, hSupport: \operatorname{tsupport}(f) \subseteq [-L, L], hZero: \operatorname{SymmetricConvergent}(Z, \operatorname{convolutionSquare}(f)), hArch: \operatorname{ArchimedeanConvergent}(\operatorname{convolutionSquare}(f)) \Rightarrow {\operatorname{zeroSum}(Z, \operatorname{convolutionSquare}(f), hZero) = 2 \lvert\int_{\mathbb{R}} \operatorname{cosh}(\frac{x}{2}) f(x) dx\rvert^{2} + \frac{1}{2\pi} \int_{\mathbb{R}} \operatorname{fixedScaleMultiplier}(L, \xi) \lvert\operatorname{fourierLaplace}(f, \xi)\rvert^{2} d\xi} \land {0 \leq \Re(\operatorname{zeroSum}(Z, \operatorname{convolutionSquare}(f), hZero)) \Leftrightarrow 0 \leq \Re(2 \lvert\int_{\mathbb{R}} \operatorname{cosh}(\frac{x}{2}) f(x) dx\rvert^{2} + \frac{1}{2\pi} \int_{\mathbb{R}} \operatorname{fixedScaleMultiplier}(L, \xi) \lvert\operatorname{fourierLaplace}(f, \xi)\rvert^{2} d\xi)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm.fixed_scale_weil_quadratic_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here W is the frozen carrier of even smooth compactly supported complex test functions. The supplied support proof places f in the fixed scale interval; hZero and hArch are exactly the convergence witnesses used by zeroSum and the frozen explicit formula. The multiplier is defined as two pi times the sum of the canonical Archimedean mu and finite prime-power PX multipliers at exp(2L). The first public conjunct is the exact complex identity, and its real part gives the second public positivity equivalence.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm.fixed_scale_weil_quadratic_form`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../TestFunctions/ConvolutionSquarePositivity.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PoleRankOneDecomposition](PoleRankOneDecomposition.md)
