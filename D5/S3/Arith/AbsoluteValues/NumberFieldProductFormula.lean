/- GID: D5/S3/Arith/AbsoluteValues/NumberFieldProductFormula
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/NumberFieldProductFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized absolute values of a nonzero number-field element have product one. -/

import Mathlib.NumberTheory.NumberField.ProductFormula

/- Library-search audit trail (2026-09-01):
   * Five-route repository searches found this atom only in `residual-open`, with empty
     `coverage_gids`, no formalization receipt, and no equivalent D5 declaration. The neighboring
     Newton-identity atom is unrelated; `HilbertReciprocityParity` only mentions an external
     product formula and explicitly does not anchor it.
   * Pinned Mathlib has the exact theorem `NumberField.prod_abs_eq_one` in
     `Mathlib.NumberTheory.NumberField.ProductFormula`; `NumberTheory.Height.NumberField` uses it
     to construct the admissible absolute-values instance. The declaration below is therefore
     only an import plus a direct application, with no second proof or auxiliary definition.
   * The source's `x ∈ Kˣ` is represented by `x : K` and `hx : x ≠ 0`. Mathlib decomposes all
     normalized places into the finite product over infinite places, weighted by `w.mult`, and the
     `finprod` over finite places. The source also gives a logarithmic equivalent; this declaration
     anchors its boxed multiplicative statement and does not add a separate logarithmic API. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.AbsoluteValues.NumberFieldProductFormula

open NumberField
open scoped BigOperators

/-- The product formula for the normalized absolute values of a number field. -/
theorem number_field_product_formula
    {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 :=
  NumberField.prod_abs_eq_one hx

#print axioms number_field_product_formula

end D5.S3.Arith.AbsoluteValues.NumberFieldProductFormula
