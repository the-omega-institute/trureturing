import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.RationalRouting.Acquisition

/-! Exact source-owned variation and dependence for actual rational acquisition. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.RationalRouting

noncomputable section
namespace Reg.D5.S3.Observer.RationalRouting.Source

/-- Exact lexical data of the endpoint execution premise. -/
abbrev RunParameters := Σ State : Type, Σ Output : Type,
  Σ _code : State → Command State Output, Σ _initial : State,
  Σ _band : Bool, Σ _finalWord : List Bool, List (List Bool × ℕ)

abbrev signature : Signature where
  Params := RunParameters
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ⟨_,_,code,init,i,v,reads⟩ out => Run code (endpoint i) init [] out v reads)
    Empty.elim

def allRuns : Realization signature := realize signature (fun _ _ _ => True) Empty.elim

def noRuns : Realization signature := realize signature (fun _ _ _ => False) Empty.elim

private def separating : RunParameters :=
  ⟨Unit,Bool,(fun _ => .halt false),(),false,[],[]⟩

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨separating,false,true,?_⟩
  intro h
  have yes : actual.readout () separating false := Run.halt rfl
  have no : ¬ actual.readout () separating true := by
    intro r
    change Run (fun _ : Unit => Command.halt false) (endpoint false) () [] true [] [] at r
    cases r with
    | halt h => cases h
    | work h _ => cases h
    | move h _ => cases h
  exact no (Eq.mp h yes)

def arena : Arena where
  signature := signature
  Law R := ∀ {State Output : Type} {code : State → Command State Output}
    {init : State} {target : ℚ → Output}, Correct code init target →
    Set.InjOn target {x | Prior x} → ∀ (i : Bool) {out : Output} {v : List Bool}
    {reads : List (List Bool × ℕ)},
      R.readout () ⟨State,Output,code,init,i,v,reads⟩ out →
      ∃ p ∈ reads, Grid p.1 p.2 (endpoint i)

private theorem rejected_law : ¬ arena.Law allRuns := by
  intro h
  have correct := actual_rational_acquisition.1
  have inj : Set.InjOn (id : ℚ → ℚ) {x | Prior x} := fun _ _ _ _ he => he
  have impossible := h correct inj false (out := endpoint false) (v := []) (reads := []) trivial
  simpa using impossible

def family : Registration arena (type_of% (@endpoint_run_requires_grid)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpoint_run_requires_grid,allRuns,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨allRuns,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_run_requires_grid) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.endpoint_run_requires_grid.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.Source.family
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
    (fun _ ⟨_,_,code,init,i,v,reads⟩ out => Run code (endpoint i) init [] out v reads) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.Source
    definition := none
    coordinates := #[0,1,2,3,7,9,10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.RationalRouting.Source
