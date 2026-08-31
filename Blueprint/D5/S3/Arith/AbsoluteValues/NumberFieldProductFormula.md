# The Product Formula for Number Fields

## Abstract

Normalized absolute values of a nonzero number-field element have product one.

**Theorem 1.1 (The normalized absolute values over all places have product one).**

$$\forall x \in K^{\times}, \prod_v \lvert x\rvert_v = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AbsoluteValues/NumberFieldProductFormula.number_field_product_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero element x of a number field K, the product of all normalized absolute values of x is one. Membership in the multiplicative group of K is represented in Lean by a nonzero x : K.

Pinned Mathlib decomposes all places into a finite product over infinite places, with each place raised to its real-or-complex multiplicity, and a finprod over finite places. The proof is the direct application NumberField.prod_abs_eq_one hx; no local reconstruction is introduced.

The source also states the logarithmic sum-zero form as an equivalent presentation. This truth anchor formalizes the boxed multiplicative statement and adds no hypotheses or separate logarithmic declaration.

## References

- Truth anchor: `D5/S3/Arith/AbsoluteValues/NumberFieldProductFormula.number_field_product_formula`
