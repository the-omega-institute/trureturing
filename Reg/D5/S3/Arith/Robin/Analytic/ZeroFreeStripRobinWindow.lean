import D5.S3.Arith.Robin.Analytic.ZeroFreeStripRobinWindow
import Reg.Support.SingleDependentReadout

/-! Observation of the terminal defect in the scaled endpoint limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Real
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Arith.Robin.Analytic.ZeroFreeStripRobinWindow
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass (endpointDefect)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripRobinWindow

private abbrev ActualStrip (alpha : ℝ) : Prop :=
  ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ => endpointDefect psiErrorKernel) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha b : ℝ}, 0 < alpha → alpha ≤ 1 / 2 → ActualStrip alpha →
    1 < b → 1 / 2 ≤ alpha * b →
    Tendsto (fun Y : ℝ => sqrt Y * max (-R.readout () () (Y ^ b)) 0) atTop (𝓝 0)

private theorem source_bridge :
    (type_of% @tendsto_sqrt_mul_negative_endpoint_of_actual_strip) ↔ arena.Law actual := Iff.rfl

private theorem actual_law : arena.Law actual :=
  source_bridge.mp @tendsto_sqrt_mul_negative_endpoint_of_actual_strip

/-- An endpoint intervention can fail the law exactly when an actual seed strip
with positive width is available. The constant defect −1 gives the rejection. -/
private theorem variation_iff_positive_seed : Variation arena actual ↔
    ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ 1 / 2 ∧ ActualStrip alpha := by
  constructor
  · rintro ⟨_, bad, hbad⟩
    by_contra hseed
    apply hbad
    intro alpha b ha hhalf hstrip _ _
    exact (hseed ⟨alpha, ha, hhalf, hstrip⟩).elim
  · rintro ⟨alpha, ha, hhalf, hstrip⟩
    let bad : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
    let b : ℝ := 1 + alpha⁻¹
    have hb : 1 < b := lt_add_of_pos_right _ (inv_pos.mpr ha)
    have hwidth : 1 / 2 ≤ alpha * b := by
      dsimp only [b]
      rw [mul_add, mul_one, mul_inv_cancel₀ ha.ne']
      linarith
    refine ⟨actual_law, bad, ?_⟩
    intro law
    have h := law ha hhalf hstrip hb hwidth
    have hzero : Tendsto sqrt atTop (𝓝 0) := by
      simpa [bad, realize] using h
    have hinfty : Tendsto (fun Y : ℝ => sqrt Y) atTop atTop := by
      simpa only [sqrt_eq_rpow] using tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    exact not_tendsto_atTop_of_tendsto_nhds hzero hinfty

end Reg.D5.S3.Arith.Robin.Analytic.ZeroFreeStripRobinWindow
