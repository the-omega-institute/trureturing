/- GID: D5/S3/Analytic/SquareOrderDescent
   generality: G
   mirror-B: D5/B/S3/Analytic/SquareOrderDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Square-root rescaling halves logarithmic maximum-modulus order. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Six-way repository retrieval searched square descent, entire-function
     order, maximum modulus, limsup under square roots, symbol/body variants,
     digestion receipts and indexes, generalized rescaling theorems, and all
     commits on `origin/lane/math/*` beyond `origin/dev`. No D5 declaration
     states this order-halving identity or its maximum-modulus hypothesis.
   * Pinned Mathlib has no packaged entire-function order API. Exact component
     hits are `Real.log_sqrt`, `Real.map_sqrt_atTop`, `limsup_comp`,
     `limsup_congr`, `EReal.limsup_const_mul_of_nonneg_of_ne_top`, and
     `Filter.eventually_gt_atTop`; these are used directly below.
   * The source omitted the relation between `F` and `G`. This theorem assumes
     its displayed maximum-modulus consequence `MG r = MF (sqrt r)` for
     nonnegative radii. It also assumes `MF` is eventually greater than one,
     so the nested logarithm has its standard growth-order meaning rather than
     relying on Lean's totalized logarithm at nonpositive arguments.
 -/

open Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SquareOrderDescent

/-- The extended-real logarithmic order attached to a radial maximum-modulus function. -/
noncomputable def radialOrder (maximumModulus : Real -> Real) : EReal :=
  limsup
    (fun radius : Real =>
      ((Real.log (Real.log (maximumModulus radius)) /
          Real.log radius : Real) : EReal))
    atTop

private theorem order_kernel_square_root
    (MF MG : Real -> Real)
    (maximum_modulus_square_root :
      forall radius, 0 <= radius -> MG radius = MF (Real.sqrt radius)) :
    ∀ᶠ radius : Real in atTop,
      ((Real.log (Real.log (MG radius)) / Real.log radius : Real) : EReal) =
        ((1 / 2 : Real) : EReal) *
          ((Real.log (Real.log (MF (Real.sqrt radius))) /
            Real.log (Real.sqrt radius) : Real) : EReal) := by
  filter_upwards [eventually_gt_atTop (1 : Real)] with radius radius_gt_one
  have radius_nonnegative : 0 <= radius := le_trans (by norm_num) radius_gt_one.le
  have log_radius_positive : 0 < Real.log radius := Real.log_pos radius_gt_one
  have real_identity :
      Real.log (Real.log (MG radius)) / Real.log radius =
        (1 / 2 : Real) *
          (Real.log (Real.log (MF (Real.sqrt radius))) /
            Real.log (Real.sqrt radius)) := by
    rw [maximum_modulus_square_root radius radius_nonnegative]
    rw [Real.log_sqrt radius_nonnegative]
    field_simp [log_radius_positive.ne']
  exact_mod_cast real_identity

private theorem radial_order_scale
    (MF MG : Real -> Real)
    (maximum_modulus_square_root :
      forall radius, 0 <= radius -> MG radius = MF (Real.sqrt radius)) :
    radialOrder MG = ((1 / 2 : Real) : EReal) * radialOrder MF := by
  unfold radialOrder
  calc
    limsup
        (fun radius : Real =>
          ((Real.log (Real.log (MG radius)) /
            Real.log radius : Real) : EReal)) atTop =
      limsup
        (fun radius : Real =>
          ((1 / 2 : Real) : EReal) *
            ((Real.log (Real.log (MF (Real.sqrt radius))) /
              Real.log (Real.sqrt radius) : Real) : EReal)) atTop :=
        limsup_congr
          (order_kernel_square_root MF MG maximum_modulus_square_root)
    _ = ((1 / 2 : Real) : EReal) *
        limsup
          (fun radius : Real =>
            ((Real.log (Real.log (MF (Real.sqrt radius))) /
              Real.log (Real.sqrt radius) : Real) : EReal)) atTop := by
      rw [EReal.limsup_const_mul_of_nonneg_of_ne_top]
      · norm_num
      · norm_num
    _ = ((1 / 2 : Real) : EReal) *
        limsup
          (fun radius : Real =>
            ((Real.log (Real.log (MF radius)) /
              Real.log radius : Real) : EReal)) atTop := by
      congr 1
      change
        limsup
          ((fun radius : Real =>
            ((Real.log (Real.log (MF radius)) /
              Real.log radius : Real) : EReal)) ∘ Real.sqrt) atTop = _
      rw [limsup_comp, Real.map_sqrt_atTop]

/-- If the radial maximum moduli satisfy the square-root rescaling identity,
then logarithmic order is halved. The eventual lower bound prevents the nested
logarithm from using its totalized nonpositive branch. -/
theorem square_order_descent
    (MF MG : Real -> Real)
    (MF_eventually_gt_one : ∀ᶠ radius : Real in atTop, 1 < MF radius)
    (maximum_modulus_square_root :
      forall radius, 0 <= radius -> MG radius = MF (Real.sqrt radius)) :
    (∀ᶠ radius : Real in atTop, 1 < MG radius) /\
      radialOrder MG = ((1 / 2 : Real) : EReal) * radialOrder MF /\
      (radialOrder MF = 1 ->
        radialOrder MG = ((1 / 2 : Real) : EReal)) := by
  have MF_sqrt_eventually_gt_one :
      ∀ᶠ radius : Real in atTop, 1 < MF (Real.sqrt radius) :=
    Real.tendsto_sqrt_atTop.eventually MF_eventually_gt_one
  have MG_eventually_gt_one : ∀ᶠ radius : Real in atTop, 1 < MG radius := by
    filter_upwards
      [MF_sqrt_eventually_gt_one, eventually_gt_atTop (0 : Real)] with
      radius MF_sqrt_gt_one radius_positive
    rw [maximum_modulus_square_root radius radius_positive.le]
    exact MF_sqrt_gt_one
  have order_scale :=
    radial_order_scale MF MG maximum_modulus_square_root
  refine ⟨MG_eventually_gt_one, order_scale, ?_⟩
  intro MF_order_one
  rw [order_scale, MF_order_one, mul_one]

#print axioms square_order_descent

end D5.S3.Analytic.SquareOrderDescent
