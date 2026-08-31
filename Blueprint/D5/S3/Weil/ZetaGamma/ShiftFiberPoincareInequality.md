# Shift-Fiber Poincare Inequality

## Abstract

A compactly supported Weil test has the sharp finite-Dirichlet spectral gap along every positive real translation.

**Theorem 1.1 (The support-controlled translation gap).**

$$\forall f\in \mathcal{W}, L, a\in \mathbb{R}, 0 < a \land \operatorname{support}\left(f\right) \subseteq [-L, L] \Rightarrow \operatorname{shiftFiberGap}\left(L, a\right) \cdot \operatorname{l2Mass}\left(f\right) \le \operatorname{translationEnergy}\left(f, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ShiftFiberPoincareInequality.shift_fiber_poincare_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical even smooth compactly supported complex Weil-test space. The displayed support premise uses the ordinary function support on the exact real interval from minus L to L.

The public count is floor(2L/a)+1. The public gap is four times the square of sin(pi/(2(count+1))), and translationEnergy uses the source shift f(x-a).

The proof applies the frozen sharp real path-averaging bound to the real and imaginary parts, obtains the complex Dirichlet path estimate, and integrates its fibers over one fundamental interval.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ShiftFiberPoincareInequality.shift_fiber_poincare_inequality`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrameTaxOptimal](../../QuantumBounds/ReferenceFrameTaxOptimal.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](ArchimedeanJumpDecomposition.md)
