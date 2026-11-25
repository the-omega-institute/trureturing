import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletRampPrimeTail
import Reg.Support.SingleDependentReadout

/-! Adding one to each normalized readout shifts its limit and breaks the source law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.CharacterSums.DirichletRampPrimeTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.CharacterSums.DirichletRampPrimeTail

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private theorem shifted_limit_fails {f : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f atTop (𝓝 c)) : ¬ Tendsto (fun x => f x + 1) atTop (𝓝 c) := by
  intro h
  have hshift : Tendsto (fun x => f x + 1) atTop (𝓝 (c + 1)) :=
    hf.add tendsto_const_nhds
  exact (ne_of_gt (lt_add_of_pos_right c zero_lt_one)) (tendsto_nhds_unique hshift h)

private theorem dependence_of_nonzero_limit {f : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f atTop (𝓝 c)) (hzero : f 0 = 0) (hc : c ≠ 0) :
    ObservationalDependence signature
      (realize signature (fun _ _ x => f x) (fun e => nomatch e)) := by
  intro i
  cases i
  refine ⟨(), 0, ?_⟩
  change ∃ x : ℝ, f 0 ≠ f x
  by_contra! hconstant
  have hconst : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 c) :=
    hf.congr' (Eventually.of_forall fun x => (hconstant x).symm.trans hzero)
  exact hc (tendsto_nhds_unique hconst tendsto_const_nhds)

namespace Root

def actual : Realization signature :=
  realize signature (fun _ _ x => HChi x / Real.sqrt x) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ x => HChi x / Real.sqrt x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun x : ℝ => R.readout () () x) atTop (𝓝 1)

private theorem shifted_fails : ¬ arena.Law shifted :=
  shifted_limit_fails HChi_root_limit

private theorem actual_dependence : ObservationalDependence signature actual :=
  dependence_of_nonzero_limit (f := fun x : ℝ => HChi x / Real.sqrt x)
    (c := (1 : ℝ)) HChi_root_limit (by simp only [Real.sqrt_zero, div_zero])
    (show (1 : ℝ) ≠ 0 from one_ne_zero)

def family : Registration arena (type_of% (@HChi_root_limit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨HChi_root_limit, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@HChi_root_limit) (Realization signature) Unit Unit where
  unitName := `D5.S3.CharacterSums.DirichletRampPrimeTail.HChi_root_limit.__information_unit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletRampPrimeTail.Root.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => HChi x / Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampPrimeTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Root

namespace RampTail

def actual : Realization signature :=
  realize signature (fun _ _ x => x * (∫ t in Ioi x, HChi t / t ^ 2) / Real.sqrt x)
    (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ x => x * (∫ t in Ioi x, HChi t / t ^ 2) / Real.sqrt x + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun x : ℝ => R.readout () () x) atTop (𝓝 2)

private theorem shifted_fails : ¬ arena.Law shifted :=
  shifted_limit_fails HChi_ramp_tail_root_limit

def family : Registration arena (type_of% @HChi_ramp_tail_root_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨HChi_ramp_tail_root_limit, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := dependence_of_nonzero_limit HChi_ramp_tail_root_limit
    (by simp only [Real.sqrt_zero, div_zero]) (by norm_num)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@HChi_ramp_tail_root_limit) (Realization signature) Unit Unit where
  unitName := `D5.S3.CharacterSums.DirichletRampPrimeTail.HChi_ramp_tail_root_limit.__information_unit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletRampPrimeTail.RampTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => x * (∫ t in Ioi x, HChi t / t ^ 2) / Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampPrimeTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RampTail

end Reg.D5.S3.CharacterSums.DirichletRampPrimeTail
