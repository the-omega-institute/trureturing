import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
open _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ZITable

/-- Observe the matrix at the table's observable index. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 9 → Matrix (Fin 4) (Fin 4) ℂ)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => f 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () obs = !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  change (0 : ℂ) = 1 at hc
  norm_num at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [actual, realize] at hc

def source_registration : Registration arena (type_of% @ZITable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ZITable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.ZITable)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.ZITable.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.ZITable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ZITable

namespace XITable

/-- Observe the matrix at the table's observable index. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 9 → Matrix (Fin 4) (Fin 4) ℂ)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => f 4) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () obs = !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 2) h
  change (0 : ℂ) = 1 at hc
  norm_num at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [actual, realize] at hc

def source_registration : Registration arena (type_of% @XITable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨XITable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.XITable)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.XITable.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.XITable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f 4) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end XITable

namespace HermitianSquare

/-- Observe left multiplication by a variable matrix at each observable index. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 9)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

def actual : Realization signature :=
  realize signature (fun _ v M => M * obs v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain Hermitian symmetry and the full square identity for every index. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v, (obs v).IsHermitian ∧ R.readout () v (obs v) = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) (h 0).2
  change (0 : ℂ) = 1 at hc
  norm_num at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [actual, realize,
    _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.ZITable] at hc

def source_registration : Registration arena (type_of% @obs_herm_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨obs_herm_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.obs_herm_sq)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.HermitianSquare.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.HermitianSquare.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ v M => M * obs v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end HermitianSquare

end
end Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
