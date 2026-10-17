import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Computability.WindowOriginalEncoder

namespace Reg.D5.S0.Computability.WindowOriginalEncoder
open PhysicalWindowContinuation PhysicalWindowContinuation.OriginalEncoder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S1.Digit.GoldenBase4AutomataOracle
open _root_.D5.S3.Arith.ZeckendorfFutureKernel
open LeanInformationAudit

namespace display_succ
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p s => display p (s+1)) (fun e => nomatch e)
def stopped : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (N k : ℕ), R.readout () N k = bit N k :: display N k

private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.OriginalEncoder.display_succ
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad 0 0
  simpa [stopped,realize] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨0,0,1,by intro h; have hh:=congrArg List.length h; simpa [actual,realize,display] using hh⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.OriginalEncoder.display_succ) where
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
    _root_.PhysicalWindowContinuation.OriginalEncoder.display_succ
    (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.OriginalEncoder.display_succ.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowOriginalEncoder.display_succ.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ p s => display p (s+1)) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowOriginalEncoder
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end display_succ

namespace original_bits
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p s => display p s) (fun e => nomatch e)
def stopped : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (h N : ℕ), NativeContinuation.NullReplyFiber.highBits (W h N) ++ [bit N 0] = R.readout () N (3*h+1)

private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.OriginalEncoder.original_bits
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad 0 0
  simpa [stopped,realize,W,NativeContinuation.NullReplyFiber.highBits] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨0,1,4,by intro h; have hh:=congrArg List.length h; simpa [actual,realize,display] using hh⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.OriginalEncoder.original_bits) where
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
    _root_.PhysicalWindowContinuation.OriginalEncoder.original_bits
    (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.OriginalEncoder.original_bits.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowOriginalEncoder.original_bits.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ p s => display p s) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowOriginalEncoder
    definition := none
    coordinates := #[1]
    readouts := #[{path := #["body","body","arg"], stateBinder := 0,stateOperand := some #["arg"], functionOperand := false, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end original_bits

namespace padded_display
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p s => display p s) (fun e => nomatch e)
def stopped : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (N k : ℕ), zeckendorfWordLength N ≤ k → (R.readout () N k).map (fun b : Bool => if b then (1 : Fin 2) else 0) = List.replicate (k-zeckendorfWordLength N) 0 ++ zeckendorfMSDWord N

private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.OriginalEncoder.padded_display
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad 0 1 (by simp [L,zeckendorfWordLength,_root_.D5.S0.Conventions.wdigits])
  have : ([] : List (Fin 2)) = [0] := by simpa [stopped,realize,L,zeckendorfWordLength,zeckendorfMSDWord,zeckendorfBit,_root_.D5.S0.Conventions.wdigits] using h
  cases this
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨0,1,2,by intro h; have hh:=congrArg List.length h; simpa [actual,realize,display] using hh⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.OriginalEncoder.padded_display) where
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
    _root_.PhysicalWindowContinuation.OriginalEncoder.padded_display
    (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.OriginalEncoder.padded_display.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowOriginalEncoder.padded_display.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ p s => display p s) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowOriginalEncoder
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body","body","body","fn","arg","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end padded_display

namespace padded_windows
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List LiteralWindowEnd.Window
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p s => W s p) (fun e => nomatch e)
def stopped : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (N h : ℕ), L N ≤ h → R.readout () N h = List.replicate (h-L N) .zero ++ W (L N) N

private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.OriginalEncoder.padded_windows
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := bad 0 1 (by simp [L,zeckendorfWordLength,_root_.D5.S0.Conventions.wdigits])
  have : ([] : List LiteralWindowEnd.Window) = [.zero] := by simpa [stopped,realize,L,zeckendorfWordLength,zeckendorfMSDWord,zeckendorfBit,_root_.D5.S0.Conventions.wdigits] using h
  cases this
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨0,0,1,by intro h; have hh := congrArg List.length h; change 0=1 at hh; omega⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.OriginalEncoder.padded_windows) where
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
    _root_.PhysicalWindowContinuation.OriginalEncoder.padded_windows
    (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.OriginalEncoder.padded_windows.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowOriginalEncoder.padded_windows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ p s => W s p) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowOriginalEncoder
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body","body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end padded_windows

namespace local_source
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Window
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p s => localWord s p) (fun e => nomatch e)
def stopped : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (h N : ℕ), L N ≤ h → (R.readout () N h).length=h ∧ legal false (NativeContinuation.NullReplyFiber.highBits ((localWord h N).map Original.letter) ++ [bit N 0]) ∧ Original.numeral (localWord h N) (bit N 0)=N

private theorem faithful : arena.Law actual := _root_.PhysicalWindowContinuation.OriginalEncoder.local_source
private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  have h := (bad 1 0 (by simp [L,zeckendorfWordLength,_root_.D5.S0.Conventions.wdigits])).1
  simpa [stopped,realize] using h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨0,0,1,by intro h; have hh := congrArg List.length h; change 0=1 at hh; omega⟩

def family : Registration arena (type_of% _root_.PhysicalWindowContinuation.OriginalEncoder.local_source) where
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
    _root_.PhysicalWindowContinuation.OriginalEncoder.local_source
    (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.OriginalEncoder.local_source.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowOriginalEncoder.local_source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ p s => localWord s p) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowOriginalEncoder
    definition := none
    coordinates := #[1]
    readouts := #[{path := #["body","body","body","fn","arg","fn","arg","arg"], stateBinder := 0,stateOperand := some #["fn","arg"], functionOperand := false, booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end local_source

end Reg.D5.S0.Computability.WindowOriginalEncoder
