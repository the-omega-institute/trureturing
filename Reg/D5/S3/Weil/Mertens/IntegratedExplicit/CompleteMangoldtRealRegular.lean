import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular
import Reg.Support.SingleDependentReadout

/-! Source selection of the original transform in the right half-plane agreement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
  (transform transform_integral_and_zero_germs)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ s => transform s) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ s => transform s + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    MeromorphicOn continued {s : ℂ | 0 < s.re} ∧
    (∀ x : ℝ, 0 < x → AnalyticAt ℂ continued (x : ℂ)) ∧
    (∀ s : ℂ, 1 < s.re → continued s = V.readout () () s)

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hs : 1 < (2 : ℂ).re := by norm_num
  have he := (continuation.2.2 2 hs).symm.trans (h.2.2 2 hs)
  change transform 2 = transform 2 + 1 at he
  exact one_ne_zero (by linear_combination -he : (1 : ℂ) = 0)

private theorem transform_depends : ObservationalDependence signature actual := by
  intro i
  by_contra! h
  have hconstant (s : ℂ) : transform s = transform (-2) := h () s (-2)
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  obtain ⟨_, hn, H, hH, hgerm⟩ := transform_integral_and_zero_germs.2 (-2) hz
  let c : ℂ := (analyticOrderNatAt riemannZeta (-2) : ℂ) / ((-2) * (1 - (-2)))
  have hzero : Tendsto (fun s : ℂ => (s - (-2)) * (transform (-2) - H s))
      (𝓝[≠] (-2)) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℂ => (s - (-2)) * (transform (-2) - H s)) (-2) :=
      (continuousAt_id.sub continuousAt_const).mul (continuousAt_const.sub hH.continuousAt)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hvalue : (fun s : ℂ => (s - (-2)) * (transform (-2) - H s)) =ᶠ[𝓝[≠] (-2)]
      fun _ => c := by
    filter_upwards [hgerm, self_mem_nhdsWithin] with s hs hne
    have hsub : s - (-2) ≠ 0 := sub_ne_zero.mpr hne
    rw [← hconstant s, hs]
    change (s - (-2)) * (c / (s - (-2)) + H s - H s) = c
    rw [add_sub_cancel_right, mul_div_cancel₀ c hsub]
  exact hn (tendsto_nhds_unique (tendsto_const_nhds (x := c)) (hzero.congr' hvalue))

def family : Registration arena (type_of% @continuation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuation, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := transform_depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@continuation) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular.continuation.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => transform s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular
