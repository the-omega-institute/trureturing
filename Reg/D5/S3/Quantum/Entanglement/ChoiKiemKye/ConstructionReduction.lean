import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
import Reg.Support.DependentFamily

/-! Source-bound audit of the alternating sign identity. -/

namespace Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
open _root_.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the alternating sign appearing in the second factor. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ i => (-1 : ℂ) ^ i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : ℕ, (-1 : ℂ) ^ i * R.readout () () i = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0
  norm_num [rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (-1 : ℂ) ^ 0 ≠ (-1 : ℂ) ^ 1
  norm_num

def source_registration : Registration arena (∀ i : ℕ, (-1 : ℂ) ^ i * (-1 : ℂ) ^ i = 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Cycle.sign_square, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

#print _root_.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Cycle.sign_square

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Cycle.sign_square)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ i => (-1 : ℂ) ^ i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
