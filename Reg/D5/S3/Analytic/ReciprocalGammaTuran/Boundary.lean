import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ReciprocalGammaTuran.Boundary

import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Defs

namespace Reg.D5.S3.Analytic.ReciprocalGammaTuran.Boundary
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Boundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ t => turanCoeff (fun _ => 1) (-t) t t 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 0 < t → t < 1 → R.readout () () t < 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (t := 1 / 2) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  change turanCoeff (fun _ => 1) (-(0 : ℝ)) 0 0 2 ≠
    turanCoeff (fun _ => 1) (-(1 / 2)) (1 / 2) (1 / 2) 2
  have hz : turanCoeff (fun _ => 1) (-(0 : ℝ)) 0 0 2 = 0 := by simp [turanCoeff]
  rw [hz]
  exact ne_of_gt (d_two_neg (t := 1 / 2) (by norm_num) (by norm_num))
def family : Registration arena (type_of% @d_two_neg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨d_two_neg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@d_two_neg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Boundary.Negative.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Boundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => turanCoeff (fun _ => 1) (-t) t t 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Boundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Analytic.ReciprocalGammaTuran.Boundary
