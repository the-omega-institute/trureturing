import Reg.D5.S3.Observer.RationalRouting.Source
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.RationalRouting.Prices

/-! Exact source-owned variation and dependence for actual rational acquisition. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.RationalRouting

noncomputable section
namespace Reg.D5.S3.Observer.RationalRouting.Acquisition

abbrev signature : Signature where
  Params := Unit
  State _ := AcquisitionState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Command AcquisitionState ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ st => acquisitionCode false st) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Command.halt 0) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(),.start,.done 0,?_⟩
  intro h
  cases h

def arena : Arena where
  signature := signature
  Law R :=
    Correct (fun st => R.readout () () st) .start id ∧
    ActionCap (acquisitionCode false) .start 2 ∧
    Correct (acquisitionCode true) .start id ∧
    ActionCap (acquisitionCode true) .start 4 ∧
    Preset (acquisitionCode true) .start (fun k => [false,false,true,false][k]?.getD false) ∧
    (∀ x, Prior x → 0 < x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Prior (endpoint false) := ⟨false,Or.inl rfl⟩
  have run : Run (fun st => rejected.readout () () st) (endpoint false)
      .start [] 0 [] [] := Run.halt rfl
  have bad := (h.1 (endpoint false) hp).2 _ _ _ run
  norm_num [endpoint,id_eq] at bad

def family : Registration arena (type_of% (@actual_rational_acquisition)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_rational_acquisition,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_rational_acquisition) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.actual_rational_acquisition.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.Acquisition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ st => acquisitionCode false st) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.Acquisition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.RationalRouting.Acquisition

namespace Reg.D5.S3.Observer.RationalRouting.RunUnique

abbrev RunParameters := Σ State : Type, Σ Output : Type,
  Σ _code : State → Command State Output, Σ _original : ℚ,
  Σ _initial : State, Σ _startWord : List Bool,
  Σ _finalWord : List Bool, List (List Bool × ℕ)

abbrev signature : Signature where
  Params := RunParameters
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ⟨_,_,code,x,st,w,v,reads⟩ out => Run code x st w out v reads) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => True) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let p : RunParameters := ⟨Unit,Bool,(fun _ => .halt false),1,(),[],[],[]⟩
  refine ⟨p,false,true,?_⟩
  intro he
  have yes : actual.readout () p false := Run.halt rfl
  have no : ¬ actual.readout () p true := by
    intro r
    change Run (fun _ : Unit => Command.halt false) 1 () [] true [] [] at r
    cases r with
    | halt h => cases h
    | work h _ => cases h
    | move h _ => cases h
  exact no (Eq.mp he yes)

def arena : Arena where
  signature := signature
  Law R := ∀ {State Output : Type} {code : State → Command State Output}
    {x : ℚ} {st : State} {w : List Bool} {out out' : Output} {v v' : List Bool}
    {reads reads' : List (List Bool × ℕ)},
    R.readout () ⟨State,Output,code,x,st,w,v,reads⟩ out →
    Run code x st w out' v' reads' → out = out' ∧ v = v' ∧ reads = reads'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have run : Run (fun _ : Unit => Command.halt false) 1 () [] false [] [] := Run.halt rfl
  have bad := h (out := true) (v := []) (reads := []) trivial run
  cases bad.1

def family : Registration arena (type_of% (@run_unique)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@run_unique,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@run_unique) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.run_unique.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.RunUnique.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ⟨_,_,code,x,st,w,v,reads⟩ out => Run code x st w out v reads) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.Acquisition
    definition := none
    coordinates := #[0,1,2,3,4,5,8,10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.RationalRouting.RunUnique
