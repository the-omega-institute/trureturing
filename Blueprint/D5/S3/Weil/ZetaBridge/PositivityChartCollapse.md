# Positivity-Chart Collapse

## Abstract

Every finite feature chart of one positive spectral measure has a positive semidefinite Gram kernel.

**Theorem 1.1 (Feature dictionaries preserve Gram positivity).**

$$\forall Omega, X: \operatorname{Type}, \operatorname{MeasurableSpace}(Omega) \land \operatorname{Finite}(X), nu: \operatorname{Measure}(Omega), Phi: X \to \operatorname{L2}(nu, \mathbb{C}) \Rightarrow\\\operatorname{PosSemidef}((x, y) \mapsto \int_{Omega} Phi(x)(gamma) overline(Phi(y)(gamma)) dnu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/PositivityChartCollapse.positivity_chart_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be a measurable space, X a finite feature index type, nu a measure, and Phi a family of complex square-integrable features. The displayed kernel is defined directly by the source integral, with no separately declared kernel object.

The matrix is the transpose of the standard complex Gram matrix. Mathlib proves that Gram matrix positive semidefinite; the local proof expands the L2 inner product and checks the conjugation orientation of the displayed integral.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/PositivityChartCollapse.positivity_chart_collapse`
