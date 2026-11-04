import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the fermionic Rényi Stieltjes representation. -/

namespace Reg.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes

open _root_.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Real Set MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

#print _root_.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.weight_pos
#print _root_.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.weight_integrable
#print _root_.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.stieltjes_representation

namespace WeightPos

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ u α => fermionicWeight α u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α u : ℝ}, 0 < α → α < 1 → 0 ≤ u → u < 1 →
    0 < R.readout () u α

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (u := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1 / 2, ?_⟩
  change fermionicWeight 0 0 ≠ fermionicWeight (1 / 2) 0
  have hp := weight_pos (α := (1 / 2 : ℝ)) (u := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [fermionicWeight] using ne_of_lt hp

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
  unitName := `Reg.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.WeightPos.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.WeightPos.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ u α => fermionicWeight α u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end WeightPos

namespace WeightIntegrable

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => (ℝ → ℝ))

def actual : Realization signature :=
  realize signature (fun _ _ α => fermionicWeight α) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ u => u ^ (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : ℝ}, 0 < α → α < 1 →
    IntegrableOn (R.readout () () α) (Ioo 0 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (by norm_num) (by norm_num)
  change IntegrableOn (fun u : ℝ => u ^ (-1 : ℝ)) (Ioo 0 1) at hb
  have hf := (intervalIntegral.integrableOn_Ioo_rpow_iff
    (s := (-1 : ℝ)) (by norm_num : (0 : ℝ) < 1)).mp hb
  exact (lt_irrefl (-1 : ℝ)) hf

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  change fermionicWeight 0 ≠ fermionicWeight (1 / 2)
  intro he
  have hv := congrFun he 0
  have hz : fermionicWeight 0 0 = 0 := by simp [fermionicWeight]
  rw [hz] at hv
  exact (ne_of_lt (weight_pos (α := (1 / 2 : ℝ)) (u := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num))) hv

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
  unitName := `Reg.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.WeightIntegrable.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes.WeightIntegrable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ α => fermionicWeight α) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end WeightIntegrable

end
end Reg.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
