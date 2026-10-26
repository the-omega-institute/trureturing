import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition

open _root_.D5.S3.Arith.FibonacciAtomic
open NativeContinuation.NullReplyFiber (NativeHistory)
open NativeContinuation.Acquisition.NativeSuffixAcquisition
open GraftAffineClosure (residue)
open ImmediateWindowStateCapacity (rawMachine)
open LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ L : ℕ, Σ _ : Fin L → Finset Window, Σ _ : Finset Bool, Fin (L + 1)
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p s => entry (counts p.2.2.1 ((List.ofFn p.2.1).drop p.2.2.2.val)) s)
  (fun e => nomatch e)

def zero : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (A : Fin L → Finset Window) (B : Finset Bool),
    let as := List.ofFn A
    (table B as).length = L + 1 ∧
    (∀ (t : Fin (L + 1)) (s : Bool),
      (table B as)[t.val]? = some (counts B (as.drop t.val)) ∧
      R.readout () ⟨L, A, B, t⟩ s = (completions B (as.drop t.val) s).card ∧
      entry (counts B (as.drop t.val)) s ≤ 5 ^ (L - t.val) ∧
      ∀ (c : ℕ × ℕ) (w : List Window),
        w ∈ completions B (as.drop t.val) s ↔
          Allowed (as.drop t.val) w ∧ ∃ u ∈ B, ∃ d : ℕ × ℕ, NativeHistory s c w u d) ∧
    (∀ s : Bool,
      ((acquire B as s).2 = none ↔ entry (counts B as) s = 0) ∧
      (entry (counts B as) s = 0 ↔
        ¬ ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),
          Allowed as w ∧ u ∈ B ∧ NativeHistory s (0, 0) w u d) ∧
      (0 < entry (counts B as) s →
        ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),
          (acquire B as s).2 = some w ∧ w.length = L ∧ Allowed as w ∧ u ∈ B ∧
          NativeHistory s (0, 0) w u d ∧
          (rawMachine 0).toDFA.evalFrom (some (s, residue 0 (0, 0))) w =
            some (u, residue 0 d)))

private theorem faithful : arena.Law actual := native_suffix_acquisition

private theorem zero_fails : ¬ arena.Law zero := by
  intro h
  have hc := ((h 0 (fun i => Fin.elim0 i) {false}).2.1 0 false).2.1
  norm_num [zero, realize, completions] at hc

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0, (fun i => Fin.elim0 i), {false}, 0⟩, false, true, ?_⟩
  norm_num [actual, realize, counts, table, terminal, entry]

def family : Registration arena (type_of% native_suffix_acquisition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful, zero, zero_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zero, ?_, ?_, zero_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := actual_dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    native_suffix_acquisition (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition.native_suffix_acquisition.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature
    (fun _ p s => entry (counts p.2.2.1 ((List.ofFn p.2.1).drop p.2.2.2.val)) s)
    (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "body", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeSuffixAcquisition
