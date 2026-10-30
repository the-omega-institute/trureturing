import D5.S3.Observer.Completion.TypedCocycleSource
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Observer.Completion.TypedCocycleSource
namespace Reg.D5.S3.Observer.Completion.TypedCocycleSource

abbrev signature : Signature where
  Params := Unit
  State _ := History
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Name
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ u => word u) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law f := ∀ (h : ℝ) (C E : Vector),
    Function.Injective (f.readout () ()) ∧
    (∀ w z, execute .p w = some z ↔
      ∃ u : History, f.readout () () u = w ∧ endpoint u = z) ∧
    (∀ u, execute .p (f.readout () () u) = some (endpoint u) ∧
      accumulate h C E .p (f.readout () () u) = some (native h C E u))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hi := (law 1 (0, 0) (0, 0)).1
  have hn := hi (a₁ := History.pre 0) (a₂ := History.pre 1) rfl
  cases hn

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), .pre 0, .pre 1, ?_⟩
  simp [actual, realize, word]

def family : Registration arena (type_of% (@source_correspondence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_correspondence, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@source_correspondence) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.Completion.TypedCocycleSource.source_correspondence.__information_unit
  realizationName := `Reg.D5.S3.Observer.Completion.TypedCocycleSource.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => word u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Completion.TypedCocycleSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Reg.D5.S3.Observer.Completion.TypedCocycleSource
