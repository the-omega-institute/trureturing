import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory LeanInformationAudit
open scoped Topology
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ => transform) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ s => transform s + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V :=
    let Φ := V.readout () ()
    (∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun y : ℝ => Complex.exp (-s*y) * (U (Real.exp y) : ℂ)) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, Complex.exp (-s*y) * (U (Real.exp y) : ℂ)) = Φ s) ∧
    ∀ ρ : ℂ, riemannZeta ρ = 0 →
      analyticOrderNatAt riemannZeta ρ ≠ 0 ∧
      (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ)) ≠ 0 ∧
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s =
          ((analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))) / (s - ρ) + H s

private lemma shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hs : 1 < (2 : ℂ).re := by norm_num
  have he := (transform_integral_and_zero_germs.1 2 hs).2.symm.trans (h.1 2 hs).2
  change transform 2 = transform 2 + 1 at he
  exact one_ne_zero (by linear_combination -he : (1 : ℂ) = 0)

private lemma variation_at_zero : ObservationalDependence signature actual := by
  intro _
  by_contra! hc
  have hc' (s : ℂ) : transform s = transform (-2) := by
    exact hc () s (-2)
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  obtain ⟨_, hn, H, hH, hEq⟩ := transform_integral_and_zero_germs.2 (-2) hz
  let c : ℂ := (analyticOrderNatAt riemannZeta (-2) : ℂ) / ((-2) * (1 - (-2)))
  have hzero : Tendsto (fun s : ℂ => (s - (-2)) * (transform (-2) - H s))
      (𝓝[≠] (-2)) (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have hcP : ContinuousAt (fun s : ℂ => (s - (-2)) * (transform (-2) - H s)) (-2) :=
      (continuousAt_id.sub continuousAt_const).mul (continuousAt_const.sub hH.continuousAt)
    simpa using hcP.tendsto
  have heq : (fun s : ℂ => (s - (-2)) * (transform (-2) - H s)) =ᶠ[𝓝[≠] (-2)] fun _ => c := by
    filter_upwards [hEq, self_mem_nhdsWithin] with s hs hne
    have hsub : s-(-2) ≠ 0 := sub_ne_zero.mpr hne
    rw [← hc' s, hs]
    change (s-(-2)) * (c/(s-(-2)) + H s - H s) = c
    field_simp
    ring
  exact hn (tendsto_nhds_unique (tendsto_const_nhds (x := c)) (hzero.congr' heq))

def evidence : Registration arena (type_of% @transform_integral_and_zero_germs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨transform_integral_and_zero_germs, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual shifted shifted_fails
  dependence := variation_at_zero

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@transform_integral_and_zero_germs) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent.transform_integral_and_zero_germs.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => transform) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
