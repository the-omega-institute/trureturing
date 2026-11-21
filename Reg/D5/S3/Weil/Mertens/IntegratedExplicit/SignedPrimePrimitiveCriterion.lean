import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion
import Reg.Support.SingleDependentReadout

/-! Source readout of the normalized signed interval integral. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion

private def window (a b : ℝ) : ℝ := ∫ x in a..b, primeTail x / Real.sqrt x

private theorem window_not_zero_everywhere {a : ℝ} (ha : 1 ≤ a) :
    ¬ ∀ x : ℝ, 1 < x → window a x = 0 := by
  intro h
  have hcont : ContinuousOn (fun x : ℝ => primeTail x / Real.sqrt x) (Ici 1) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi.div Real.continuous_sqrt.continuousOn
      (fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)).ne')
  have htail (x : ℝ) (hx : 1 < x) : primeTail x = 0 := by
    have hi : IntervalIntegrable (fun t : ℝ => primeTail t / Real.sqrt t) volume a x :=
      (hcont.mono (fun _ ht => le_trans (le_min ha hx.le) ht.1)).intervalIntegrable
    have hc := hcont.continuousAt (Ici_mem_nhds hx)
    have hd : HasDerivAt (window a) (primeTail x / Real.sqrt x) x :=
      intervalIntegral.integral_hasDerivAt_right hi
        (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
          (hcont.aestronglyMeasurable (μ := volume) measurableSet_Ici) (Ici_mem_nhds hx)) hc
    have hlocal : window a =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      (lt_mem_nhds hx).mono fun t ht => h t ht
    have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hlocal
    exact (div_eq_zero_iff.mp (hd.deriv.symm.trans hz.deriv)).resolve_right
      (Real.sqrt_pos.mpr (by linarith)).ne'
  let u : ℝ := 4 / 3
  let v : ℝ := 3 / 2
  have huv : u ≤ v := by norm_num [u, v]
  have hsub : (∫ t in u..v, (Chebyshev.theta t - t) / t ^ 2) = 0 := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi (prime_integrable.mono_set
      (Ioi_subset_Ioi (show 1 ≤ u by norm_num [u]))) huv]
    change primeTail u - primeTail v = 0
    rw [htail u (by norm_num [u]), htail v (by norm_num [v]), sub_self]
  have hneg : (∫ t in u..v, (Chebyshev.theta t - t) / t ^ 2) = -Real.log (v / u) := by
    rw [← integral_inv_of_pos (show 0 < u by norm_num [u]) (show 0 < v by norm_num [v]),
      ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le huv] at ht
    have hzero := Chebyshev.theta_eq_zero_of_lt_two (ht.2.trans_lt (show v < 2 by norm_num [v]))
    have ht0 : t ≠ 0 := (show 0 < u by norm_num [u]).trans_le ht.1 |>.ne'
    change (Chebyshev.theta t - t) / t ^ 2 = -t⁻¹
    rw [hzero]
    field_simp
    ring
  have hpos : 0 < Real.log (v / u) := Real.log_pos (by norm_num [u, v])
  linarith

abbrev slopeSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def slopeReadout (_ _ : Unit) (T : ℝ) : ℝ :=
  (∫ x in (5040 : ℝ)..Real.exp T, primeTail x / Real.sqrt x) / T

def slopeActual : Realization slopeSignature :=
  realize slopeSignature slopeReadout (fun e => nomatch e)

abbrev slopeArena : Arena where
  signature := slopeSignature
  Law V :=
    RiemannHypothesis ↔ Tendsto (fun T : ℝ => V.readout () () T) atTop (𝓝 (-2 : ℝ))

private theorem slope_depends : ObservationalDependence slopeSignature slopeActual := by
  intro i
  cases i
  by_contra! h
  apply window_not_zero_everywhere (a := 5040) (by norm_num)
  intro x hx
  have hlo : 0 < Real.log x := Real.log_pos hx
  have h0 : slopeReadout () () 0 = 0 := by simp [slopeReadout]
  have he : slopeReadout () () (Real.log x) = 0 := (h () (Real.log x) 0).trans h0
  change window 5040 (Real.exp (Real.log x)) / Real.log x = 0 at he
  rw [Real.exp_log (zero_lt_one.trans hx)] at he
  exact (div_eq_zero_iff.mp he).resolve_right hlo.ne'

/-- Swap the target slope and the zero slope according to the original limit test. -/
private noncomputable def alternateSlope : ℝ := by
  classical
  exact if Tendsto (fun T => slopeReadout () () T) atTop (𝓝 (-2 : ℝ)) then 0 else -2

private def slopeAlternate : Realization slopeSignature :=
  realize slopeSignature (fun _ _ _ => alternateSlope) (fun e => nomatch e)

private theorem slope_alternate_fails : ¬ slopeArena.Law slopeAlternate := by
  classical
  intro h
  change (RiemannHypothesis ↔ Tendsto (fun _ : ℝ => alternateSlope) atTop (𝓝 (-2 : ℝ))) at h
  rw [tendsto_const_nhds_iff] at h
  by_cases hl : Tendsto (fun T => slopeReadout () () T) atTop (𝓝 (-2 : ℝ))
  · have hn := h.mp (rh_iff_signedPrimePrimitive_slope_from_5040.mpr hl)
    norm_num [alternateSlope, hl] at hn
  · apply hl
    exact rh_iff_signedPrimePrimitive_slope_from_5040.mp
      (h.mpr (by simp [alternateSlope, hl]))

def slopeFamily :
    Registration slopeArena (type_of% @rh_iff_signedPrimePrimitive_slope_from_5040) where
  actual := slopeActual
  bridge := Iff.rfl
  variation := ⟨rh_iff_signedPrimePrimitive_slope_from_5040, slopeAlternate, slope_alternate_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    slopeArena.Law slopeActual slopeAlternate slope_alternate_fails
  dependence := slope_depends

def slopeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rh_iff_signedPrimePrimitive_slope_from_5040) (Realization slopeSignature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion.rh_iff_signedPrimePrimitive_slope_from_5040.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion.slopeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨slopeArena⟩
  objectArena := .source ⟨slopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source slopeArena ⟨slopeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize slopeSignature slopeReadout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimePrimitiveCriterion
