import Reg.D5.S3.Observer.RationalRouting.Source
import D5.S3.Observer.RationalRouting.LowerBounds

/-! Exact source-owned variation and dependence for actual rational acquisition. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.RationalRouting

noncomputable section
namespace Reg.D5.S3.Observer.RationalRouting.LowerBounds

abbrev CapParameters := Σ State : Type, Σ Output : Type,
  Σ _code : State → Command State Output, State

abbrev signature : Signature where
  Params := CapParameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ⟨_,_,code,init⟩ h => ActionCap code init h) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => True) Empty.elim

private def acquiring : CapParameters :=
  ⟨AcquisitionState,ℚ,acquisitionCode false,.start⟩

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨acquiring,1,2,?_⟩
  intro he
  have yes : actual.readout () acquiring 2 := actual_rational_acquisition.2.1
  have bad : ActionCap (acquisitionCode false) .start 1 := Eq.mpr he yes
  have inj : Set.InjOn (id : ℚ → ℚ) {x | Prior x} := fun _ _ _ _ h => h
  have h := (original_action_lower_bounds actual_rational_acquisition.1 inj).1 1 bad
  omega

def arena : Arena where
  signature := signature
  Law R := ∀ {State Output : Type} {code : State → Command State Output}
    {init : State} {target : ℚ → Output}, Correct code init target →
    Set.InjOn target {x | Prior x} →
    (∀ h, R.readout () ⟨State,Output,code,init⟩ h → 2 ≤ h) ∧
    (∀ schedule, Preset code init schedule → ∀ h, R.readout () ⟨State,Output,code,init⟩ h → 4 ≤ h)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have correct := actual_rational_acquisition.1
  have inj : Set.InjOn (id : ℚ → ℚ) {x | Prior x} := fun _ _ _ _ he => he
  have impossible := (h correct inj).1 0 trivial
  exact (by decide : ¬ (2 : ℕ) ≤ 0) impossible

def family : Registration arena (type_of% (@original_action_lower_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_action_lower_bounds,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_action_lower_bounds) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.original_action_lower_bounds.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.LowerBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ ⟨_,_,code,init⟩ h => ActionCap code init h) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.LowerBounds
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","body","domain"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.RationalRouting.LowerBounds
