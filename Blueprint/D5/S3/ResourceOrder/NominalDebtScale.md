# Fixed Nominal Debt and Price Scale

## Abstract

Fixed nominal debt burden transforms contravariantly under uniform price scaling.

**Theorem 1.1 (Fixed nominal debt burden scales inversely).**

$$\forall D, p, \lambda \in \mathbb{R},\ 0<D \land 0<p \land 0<\lambda \Rightarrow \frac{D}{\lambda\cdot p} = \frac{1}{\lambda}\cdot \frac{D}{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/NominalDebtScale.fixed_nominal_debt_burden_scales_inversely` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive nominal debt D, positive commodity price p, and positive uniform scale lambda, holding D fixed while replacing p by lambda p multiplies the real burden D/p by 1/lambda.

Pinned Mathlib and Loogle both identify div_mul_eq_div_mul_one_div as the exact division-by-a-product lemma. The Lean proof applies that result and only reorders commutative factors.

This closes the displayed scaling identity in qdo-v1 corollary/34.2. The surrounding claims about inflation, deflation, and balance-sheet effects are explanatory consequences and are not separately formalized.

## References

- Truth anchor: `D5/S3/ResourceOrder/NominalDebtScale.fixed_nominal_debt_burden_scales_inversely`
