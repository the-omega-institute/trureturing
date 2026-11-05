import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the complex sum over an integer half-open interval. -/

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℤ (fun _ => ℤ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ a b => ∑ x ∈ Finset.Ico a b, (x : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℤ) (_hab : a ≤ b),
    R.readout () a b = ((a : ℂ) + b - 1) * ((b : ℂ) - a) / 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0 le_rfl
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 2, ?_⟩
  change (∑ x ∈ Finset.Ico (0 : ℤ) 0, (x : ℂ)) ≠
    ∑ x ∈ Finset.Ico (0 : ℤ) 2, (x : ℂ)
  rw [sum_Ico_id 0 0 le_rfl, sum_Ico_id 0 2 (by norm_num)]
  norm_num

def source_registration : Registration arena (type_of% (@sum_Ico_id)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_Ico_id, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sum_Ico_id) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum.source_registration
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
    (fun _ a b => ∑ x ∈ Finset.Ico a b, (x : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.VertexAlgebra.LatticeHalfFockBoundary.sum_Ico_id
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum
