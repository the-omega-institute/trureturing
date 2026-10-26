import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord

open _root_.D5.S3.Arith.FibonacciAtomic
open NativeContinuation.Acquisition.NativeBinaryWord
open NativeContinuation.Acquisition.NativeSuffixAcquisition (entry counts table pick reconstruct Allowed modes)
open LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ L : ℕ, Σ _ : Fin L → Finset Window, Σ _ : Finset Bool, Σ _ : Bool, Fin (L+1)
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p b => entry (counts p.2.2.1 ((List.ofFn p.2.1).drop p.2.2.2.2.val)) b) (fun e => nomatch e)
def alternate : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (A : Fin L → Finset Window) (B : Finset Bool) (s : Bool),
    let as := List.ofFn A
    let answer := reconstruct B as (table B as) s
    (input B as s).length = 3+5*L ∧
    _root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable.decodeTable L (_root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable.records B as) = table B as ∧
    (∀ (t : Fin (L+1)) (b : Bool),
      (_root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable.decodeTable L (_root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable.records B as))[t.val]? =
        some (counts B (as.drop t.val)) ∧
      R.readout () ⟨L,A,B,s,t⟩ b = (NativeContinuation.Acquisition.NativeSuffixAcquisition.completions B (as.drop t.val) b).card ∧
      entry (counts B (as.drop t.val)) b ≤ 5^(L-t.val)) ∧
    (answer = none ↔ entry (counts B as) s = 0) ∧
    (entry (counts B as) s = 0 ↔
      ¬ ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),
        Allowed as w ∧ u ∈ B ∧ _root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.NativeHistory s (0,0) w u d) ∧
    (0 < entry (counts B as) s →
      ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),
        answer = some w ∧ w.length = L ∧ Allowed as w ∧ u ∈ B ∧
        _root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.NativeHistory s (0,0) w u d ∧
        (ImmediateWindowStateCapacity.rawMachine 0).toDFA.evalFrom
          (some (s,GraftAffineClosure.residue 0 (0,0))) w = some (u,GraftAffineClosure.residue 0 d) ∧
        decodeWord (printed w) = some w) ∧
    ∃ time tape, time ≤ 1073741824 * (L+1)^4 ∧
      Complexity.runInput binaryMachine time (input B as s) = some (answer.isSome,tape) ∧
      tape.output = output B as s ∧
      _root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable.decodeTable L (tape.output.take ((L+1)*(6*L+5))) = table B as ∧
      decodeAnswer (tape.output.drop ((L+1)*(6*L+5))) = some answer

private theorem faithful : arena.Law actual := native_binary_word
private theorem alternate_fails : ¬ arena.Law alternate := by
  intro h
  have hc := ((h 0 (fun i => Fin.elim0 i) {false} false).2.2.1 0 false).2.1
  norm_num [alternate,realize,NativeContinuation.Acquisition.NativeSuffixAcquisition.completions,
    Finset.mem_singleton] at hc
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0,(fun i => Fin.elim0 i),{false},false,0⟩,false,true,?_⟩
  norm_num [actual,realize,counts,table,
    NativeContinuation.Acquisition.NativeSuffixAcquisition.terminal,entry,Finset.mem_singleton]

def family : Registration arena (type_of% native_binary_word) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,alternate,alternate_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alternate,?_,?_,alternate_fails⟩
      · intro other ho; cases role; cases other; exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    native_binary_word (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord.native_binary_word.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ p b => entry (counts p.2.2.1 ((List.ofFn p.2.1).drop p.2.2.2.2.val)) b) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord
    definition := none
    coordinates := #[0,1,2,3,6]
    readouts := #[{ path := #["body","body","body","body","body","body",
                      "arg","arg","fn","arg","body","body","arg","fn","arg","fn","arg"]
                    stateBinder := 7
                    functionOperand := false
                    stateOperand := none
                    booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord
