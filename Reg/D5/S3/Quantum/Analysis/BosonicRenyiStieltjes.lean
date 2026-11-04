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
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end WeightPos

end
end Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
