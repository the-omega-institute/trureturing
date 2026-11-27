import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115
import Reg.Support.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115

open _root_.D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Config
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Config
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => step^[3] s) (fun e => nomatch e)

private def zeroState : Config := (fun _ => false, fun _ => false)
private def oneState : Config := (fun _ => true, fun _ => true)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => oneState) (fun e => nomatch e)

/-- Preserve the complete source theorem, replacing only the three-step output. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Config, Set.Finite {i : ℤ | s.1 i = true ∨ s.2 i = true} →
    step^[9] s = s → R.readout () () s = s

private theorem zero_finite : Set.Finite {i : ℤ | zeroState.1 i = true ∨ zeroState.2 i = true} := by
  simpa [zeroState] using (Set.finite_empty : (∅ : Set ℤ).Finite)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : oneState = zeroState := h zeroState zero_finite (by rfl)
  have hc : true = false := congrArg (fun s : Config => s.1 0) he
  cases hc

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), zeroState, oneState, ?_⟩
  intro h
  have hc : false = true := congrArg (fun s : Config => s.1 0) h
  cases hc

def source_registration : Registration arena (type_of% @returns_three_of_returns_nine) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨returns_three_of_returns_nine, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro i
      exact nomatch i
  dependence := actual_dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@returns_three_of_returns_nine) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => step^[3] s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115
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

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115
