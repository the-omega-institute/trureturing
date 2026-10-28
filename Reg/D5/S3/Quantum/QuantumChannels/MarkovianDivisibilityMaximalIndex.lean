import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex
import Reg.Support.DependentFamily

/-! Source-bound audit of the greatest admissible index. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex

open _root_.D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the maximal-index coordinate as the dimension varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => 2 * d - 5) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 6) (fun e => nomatch e)

/-- Retain the universal maximality statement and the three-dimensional boundary. -/
abbrev arena : Arena where
  signature := signature
  Law r := (∀ d : ℕ, 5 ≤ d → IsGreatest (admissibleIndices d) (r.readout () () d)) ∧
    IsGreatest (admissibleIndices 3) 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (result.1 5 (by decide)).2 (h.1 5 (by decide)).1
  change 6 ≤ 2 * 5 - 5 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 5, 6, ?_⟩
  change 2 * 5 - 5 ≠ 2 * 6 - 5
  norm_num

def source_registration : Registration arena
    ((∀ d : ℕ, 5 ≤ d → IsGreatest (admissibleIndices d) (2 * d - 5)) ∧
      IsGreatest (admissibleIndices 3) 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex.source_registration
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
    (realize signature (fun _ _ d => 2 * d - 5) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg"]
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
end Reg.D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex
