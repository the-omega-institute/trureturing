# Pole-Layer Coefficient Selection

## Abstract

A shifted inverse-power series selects its pole-layer coefficient by index subtraction.

**Theorem 1.1 (A fourth-order shift selects the corresponding coefficient layer).**

$$4k\leq a,\quad[u^a](\frac{(-1)^{k-1}}{k}ru^{4k}R(u)^{-k})=\frac{(-1)^{k-1}}{k}r[u^{a-4k}]R(u)^{-k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PoleLayerSelection.pole_layer_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive order k, a row a at least 4k, a rational-coefficient power series R, and a rational residue product r, the coefficient of the shifted signed inverse power at row a equals the same scalar times the coefficient of R to the negative k at row a minus 4k.

This is a thin honest assembly over pinned Mathlib's power-series coefficient shift and constant-scaling declarations. Mathlib has no named theorem for the source atom's pole-layer specialization. The declaration proves the exact algebraic selection formula; it does not assert analytic continuation, existence of poles, or the atom's five external row calculations.

## References

- Truth anchor: `D5/S3/Analytic/PoleLayerSelection.pole_layer_coefficient`
