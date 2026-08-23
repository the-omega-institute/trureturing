/- GID: D5/S3/ResourceOrder/PriceCoordinates/BudgetSetScaleInvariance
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/PriceCoordinates/BudgetSetScaleInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Simultaneous positive scaling of prices and wealth preserves the budget set. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-23):
   * Repository search found only `fixed_nominal_debt_burden_scales_inversely`,
     which holds nominal debt fixed and proves a different inverse-scaling law.
   * Pinned Mathlib has no exact equality theorem for these budget sets.
     Its exact supporting hits `smul_dotProduct` and
     `mul_le_mul_iff_of_pos_left` are applied below. -/

namespace D5.S3.ResourceOrder.PriceCoordinates.BudgetSetScaleInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Scaling every strictly positive price and positive nominal wealth by the
same positive factor preserves exactly the nonnegative affordable bundles. -/
theorem budget_set_scale_invariance
    {L : Nat} (price : Fin L -> Real) (wealth scale : Real)
    (_hprice : forall i, 0 < price i) (_hwealth : 0 < wealth) (hscale : 0 < scale) :
    {bundle : Fin L -> Real |
        (forall i, 0 <= bundle i) /\
          dotProduct (scale • price) bundle <= scale * wealth} =
      {bundle : Fin L -> Real |
        (forall i, 0 <= bundle i) /\ dotProduct price bundle <= wealth} := by
  ext bundle
  simp only [Set.mem_setOf_eq, smul_dotProduct, smul_eq_mul]
  constructor
  case mp =>
    intro hBundle
    exact And.intro hBundle.1 ((mul_le_mul_iff_of_pos_left hscale).mp hBundle.2)
  case mpr =>
    intro hBundle
    exact And.intro hBundle.1 ((mul_le_mul_iff_of_pos_left hscale).mpr hBundle.2)

example :
    (forall i : Fin 2, 0 < (fun _ : Fin 2 => (1 : Real)) i) /\
      0 < (1 : Real) /\ 0 < (2 : Real) := by
  norm_num

example :
    {bundle : Fin 2 -> Real |
        (forall i, 0 <= bundle i) /\
          dotProduct ((2 : Real) • fun _ => (1 : Real)) bundle <= 2 * 1} =
      {bundle : Fin 2 -> Real |
        (forall i, 0 <= bundle i) /\
          dotProduct (fun _ => (1 : Real)) bundle <= 1} := by
  apply budget_set_scale_invariance
  all_goals norm_num

#print axioms budget_set_scale_invariance

end D5.S3.ResourceOrder.PriceCoordinates.BudgetSetScaleInvariance
