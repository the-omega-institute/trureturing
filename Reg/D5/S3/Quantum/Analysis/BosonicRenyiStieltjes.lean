import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the bosonic Renyi Stieltjes representation. -/

namespace Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes

open _root_.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Real Set MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace WeightPos

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x α => renyiWeight α x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α x : ℝ}, 0 < α → α < 2 → α ≠ 1 →
    0 ≤ x → x < 1 → 0 < R.readout () x α

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (x := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1 / 2, ?_⟩
  change renyiWeight 0 0 ≠ renyiWeight (1 / 2) 0
  have hp := weight_pos (α := (1 / 2 : ℝ)) (x := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [renyiWeight] using ne_of_lt hp

def source_registration : Registration arena (type_of% @weight_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weight_pos) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.WeightPos.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.WeightPos.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x α => renyiWeight α x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end WeightPos

namespace WeightIntegrable

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => (ℝ → ℝ))

def actual : Realization signature :=
  realize signature (fun _ _ α => renyiWeight α) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ x => x ^ (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : ℝ}, 0 < α → α < 2 → α ≠ 1 →
    IntegrableOn (R.readout () () α) (Ioo 0 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  change IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo 0 1) at hb
  have hf := (intervalIntegral.integrableOn_Ioo_rpow_iff
    (s := (-1 : ℝ)) (by norm_num : (0 : ℝ) < 1)).mp hb
  exact (lt_irrefl (-1 : ℝ)) hf

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  change renyiWeight 0 ≠ renyiWeight (1 / 2)
  intro he
  have hv := congrFun he 0
  have hz : renyiWeight 0 0 = 0 := by simp [renyiWeight]
  rw [hz] at hv
  exact (ne_of_lt (weight_pos (α := (1 / 2 : ℝ)) (x := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) hv

def source_registration : Registration arena (type_of% @weight_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_integrable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weight_integrable) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.WeightIntegrable.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.WeightIntegrable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ α => renyiWeight α) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end WeightIntegrable

namespace WeightMass

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ α => ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : ℝ}, 0 < α → α < 2 → α ≠ 1 → R.readout () () α = 1 / 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  change (∫ x in Ioo (0 : ℝ) 1, renyiWeight 0 x) ≠
    ∫ x in Ioo (0 : ℝ) 1, renyiWeight (1 / 2) x
  rw [weight_mass (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [renyiWeight]

def source_registration : Registration arena (type_of% @weight_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_mass, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weight_mass) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.WeightMass
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.WeightMass
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ α => ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end WeightMass

namespace StieltjesRepresentation

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ α ν => renyiFunction α ν) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α ν : ℝ}, 0 < α → α < 2 → α ≠ 1 → 1 ≤ ν →
    IntegrableOn (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) (Ioo 0 1) ∧
      R.readout () α ν = renyiConstant α +
        ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (α := 1 / 2) (ν := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  have ha := (stieltjes_representation (α := 1 / 2) (ν := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  change (1 : ℝ) = _ at hb
  have hz : renyiFunction (1 / 2) 1 = 0 := by norm_num [renyiFunction]
  rw [hz] at ha
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, 3, ?_⟩
  change renyiFunction 2 1 ≠ renyiFunction 2 3
  have hz : renyiFunction 2 1 = 0 := by norm_num [renyiFunction]
  have ht : renyiFunction 2 3 = Real.log 3 := by norm_num [renyiFunction, Real.rpow_two]
  rw [hz, ht]
  exact ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 3))

def source_registration : Registration arena (type_of% @stieltjes_representation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stieltjes_representation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@stieltjes_representation) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.StieltjesRepresentation
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.StieltjesRepresentation
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ α ν => renyiFunction α ν) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end StieltjesRepresentation




end
end Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
