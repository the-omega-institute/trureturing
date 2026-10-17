import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Computability.WindowRegisterCore

namespace Reg.D5.S0.Computability.WindowRegisterCore
open PhysicalWindowContinuation PhysicalWindowContinuation.RegisterHandoff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace stripped_false
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ bs => stripped (bs++[false])) (fun e => nomatch e)
def stopped : Realization signature :=
  realize signature (fun _ _ _ => [true]) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (bs : List Bool), R.readout () () bs = stripped bs
private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.RegisterHandoff.stripped_false
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad []
  simpa [stopped,realize,stripped] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), [], [true], by intro h; simpa [actual,realize,stripped] using h⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.RegisterHandoff.stripped_false) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped, ?_, ?_, stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    _root_.PhysicalWindowContinuation.RegisterHandoff.stripped_false (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.RegisterHandoff.stripped_false.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowRegisterCore.stripped_false.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ bs => stripped (bs++[false])) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowRegisterCore
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end stripped_false

namespace stripped_true
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ bs => stripped (bs++[true])) (fun e => nomatch e)
def stopped : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (bs : List Bool), R.readout () () bs = bs++[true]
private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.RegisterHandoff.stripped_true
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad []
  simpa [stopped,realize] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), [], [false], by intro h; simpa [actual,realize,stripped] using h⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.RegisterHandoff.stripped_true) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped, ?_, ?_, stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    _root_.PhysicalWindowContinuation.RegisterHandoff.stripped_true (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.RegisterHandoff.stripped_true.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowRegisterCore.stripped_true.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ bs => stripped (bs++[true])) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowRegisterCore
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end stripped_true

namespace normalized_false
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ bs => normalized (bs++[false])) (fun e => nomatch e)
def stopped : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (bs : List Bool), R.readout () () bs = normalized bs
private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_false
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad []
  simpa [stopped,realize,normalized,stripped] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), [], [true], by intro h; simpa [actual,realize,normalized,stripped] using h⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_false) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped, ?_, ?_, stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_false (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.RegisterHandoff.normalized_false.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowRegisterCore.normalized_false.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ bs => normalized (bs++[false])) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowRegisterCore
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end normalized_false

namespace normalized_true
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ bs => normalized (bs++[true])) (fun e => nomatch e)
def stopped : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (bs : List Bool), R.readout () () bs = bs++[true]
private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_true
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad []
  simpa [stopped,realize] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), [], [false], by intro h; simpa [actual,realize,normalized,stripped] using h⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_true) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped, ?_, ?_, stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_true (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.RegisterHandoff.normalized_true.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowRegisterCore.normalized_true.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ bs => normalized (bs++[true])) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowRegisterCore
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end normalized_true

namespace normalized_length
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ bs => normalized bs) (fun e => nomatch e)
def stopped : Realization signature :=
  realize signature (fun _ _ _ => [false,false]) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (bs : List Bool), (R.readout () () bs).length ≤ bs.length+1
private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_length
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad []
  norm_num [stopped,realize] at h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), [], [true], by intro h; simpa [actual,realize,normalized,stripped] using h⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_length) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped, ?_, ?_, stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_length (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.RegisterHandoff.normalized_length.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowRegisterCore.normalized_length.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ bs => normalized bs) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowRegisterCore
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","fn","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end normalized_length

namespace normalized_value
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ bs => normalized bs) (fun e => nomatch e)
def stopped : Realization signature :=
  realize signature (fun _ _ _ => [true]) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (bs : List Bool), Nat.ofDigits 2 ((R.readout () () bs).map Bool.toNat) = Nat.ofDigits 2 (bs.map Bool.toNat)
private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_value
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad []
  simpa [stopped,realize,Nat.ofDigits] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), [], [true], by intro h; simpa [actual,realize,normalized,stripped] using h⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_value) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped, ?_, ?_, stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_value (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.RegisterHandoff.normalized_value.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowRegisterCore.normalized_value.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ bs => normalized bs) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowRegisterCore
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","fn","arg","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end normalized_value

namespace normalized_shape
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ bs => normalized bs) (fun e => nomatch e)
def stopped : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (bs : List Bool), R.readout () () bs=[false] ∨ ∃ pre, normalized bs=pre++[true]
private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_shape
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  rcases bad [] with h | ⟨pre,h⟩
  · simpa [stopped,realize] using h
  · have hh := congrArg (fun xs : List Bool => xs.reverse.head?) h
    simp [normalized,stripped,List.reverse_append] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), [], [true], by intro h; simpa [actual,realize,normalized,stripped] using h⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_shape) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped, ?_, ?_, stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    _root_.PhysicalWindowContinuation.RegisterHandoff.normalized_shape (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.RegisterHandoff.normalized_shape.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowRegisterCore.normalized_shape.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ bs => normalized bs) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowRegisterCore
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","fn","arg","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end normalized_shape

end Reg.D5.S0.Computability.WindowRegisterCore
