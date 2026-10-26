import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable

open _root_.D5.S3.Arith.FibonacciAtomic
open NativeContinuation.Acquisition.NativeBinaryTable
open NativeContinuation.Acquisition.NativeSuffixAcquisition (entry counts completions table)
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
  (fun _ p s => entry (counts p.2.2.1 ((List.ofFn p.2.1).drop p.2.2.2.val)) s) (fun e => nomatch e)
def alternate : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (A : Fin L → Finset Window) (B : Finset Bool),
    let as := List.ofFn A
    (input B as).length = 2 + 5 * L ∧
    (records B as).length = (L + 1) * (6 * L + 5) ∧
    decodeTable L (records B as) = table B as ∧
    (∀ (t : Fin (L + 1)) (s : Bool),
      (decodeTable L (records B as))[t.val]? = some (counts B (as.drop t.val)) ∧
      R.readout () ⟨L, A, B, t⟩ s = (completions B (as.drop t.val) s).card ∧
      entry (counts B (as.drop t.val)) s ≤ 5 ^ (L - t.val)) ∧
    ∃ time tape, time ≤ 2097152 * (L + 1) ^ 4 ∧
      Complexity.runInput binaryMachine time (input B as) = some (true, tape) ∧
      tape.output = records B as

private theorem faithful : arena.Law actual := native_binary_table

private theorem alternate_fails : ¬ arena.Law alternate := by
  intro h
  have hc := ((h 0 (fun i => Fin.elim0 i) {false}).2.2.2.1 0 false).2.1
  norm_num [alternate, realize, completions] at hc

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0, (fun i => Fin.elim0 i), {false}, 0⟩, false, true, ?_⟩
  norm_num [actual, realize, counts, table,
    NativeContinuation.Acquisition.NativeSuffixAcquisition.terminal, entry]

def family : Registration arena (type_of% native_binary_table) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful, alternate, alternate_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alternate, ?_, ?_, alternate_fails⟩
      · intro other ho; cases role; cases other; exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    native_binary_table (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable.native_binary_table.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable.family
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
    (fun _ p s => entry (counts p.2.2.1 ((List.ofFn p.2.1).drop p.2.2.2.val)) s) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg",
                      "body", "body", "arg", "fn", "arg", "fn", "arg"]
                    stateBinder := 5
                    functionOperand := false
                    stateOperand := none
                    booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable
