import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathFloorCertificate
import Reg.Support.SingleDependentReadout

/-! Source-bound audit for the seven arithmetic comparisons consumed by the full triangle bound. -/
namespace Reg.D5.S3.Quantum.Recovery.FourPathFloorCertificate
open _root_.D5.S3.Quantum.Recovery.FourPathFloorCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 7) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ i => segmentNonroot i+segmentRadical i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ i : Fin 7, A.readout () () i < (49359:ℝ)/40000

theorem rejected_law : ¬ arena.Law rejected := by
  intro hv
  have hv' := hv 0
  norm_num [rejected,realize] at hv'

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize,segmentNonroot,segmentRadical]

def source_registration : Registration arena
    (∀ i : Fin 7, segmentNonroot i+segmentRadical i < (49359:ℝ)/40000) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨segment_majorants_lt_floor,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Recovery.FourPathFloorCertificate.segment_majorants_lt_floor)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathFloorCertificate.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathFloorCertificate.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => segmentNonroot i+segmentRadical i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathFloorCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.Quantum.Recovery.FourPathFloorCertificate
