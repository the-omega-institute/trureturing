# Exact Fourth-Order Pole-Layer Selection

## Abstract

Fourth-order pole layers select quotient and remainder, with nine exact row certificates.

**Theorem 1.1 (Fourth-order layers give nine exact selections).**

$$K(a)=\lfloor\frac{a}{4}\rfloor,\quad j(a)=a \operatorname{mod} 4\in{0,1,2,3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExactPoleLayerSelection.exact_pole_layer_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every row a decomposes uniquely as four times its selected order a/4 plus the remainder layer a mod 4, and the layer is strictly below four. For a at least four this makes the selected order positive, excluding the zero-denominator branch in the signed coefficient factor. The existing power-series shift theorem then reads exactly the remainder coefficient.

The rows 4, 8, 9, 12, 13, 14, 15, 16, and 17 are normalized in Lean to their nine claimed order-layer pairs. The rational regular head 1 + 2u - 2u^2 - 2u^3 gives the exact deeper readings 30, -122, and -8 after inversion and powering. These are algebraic certificates; the source's fitted tail polynomials, empirical start points, analytic pole claims, and next-layer interference mechanism require separate premises and are not asserted here.

Repository and pinned-Mathlib searches found no theorem combining this source-specific layer selection with its nine rows. The proof uses Nat.mod_add_div and Nat.mod_lt for the quotient-remainder law, and reuses the adjacent frozen pole_layer_coefficient theorem for the coefficient shift.

## References

- Truth anchor: `D5/S3/Analytic/ExactPoleLayerSelection.exact_pole_layer_selection`
- Dependency: [D5/S3/Analytic/PoleLayerSelection](PoleLayerSelection.md)
