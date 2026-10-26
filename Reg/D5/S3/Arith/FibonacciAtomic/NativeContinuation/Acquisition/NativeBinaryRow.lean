import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow

open _root_.D5.S3.Arith.FibonacciAtomic
open NativeContinuation.Acquisition.NativeBinaryRow
open NativeContinuation.Acquisition.NativeSuffixAcquisition (advance entry)
open LiteralWindowEnd (Window first last)
open Lax51Proofs.RamToTM (bitsValue)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Finset Window
  State _ := List Column
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => decode (serialize (columns a (0, 0) xs))) (fun e => nomatch e)

def zero : Realization signature := realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a : Finset Window) (xs : List Column),
    (input a xs).length = 5 + 2 * xs.length ∧
    (serialize (columns a (0, 0) xs)).length = 2 * (xs.length + 3) ∧
    R.readout () a xs = advance a (value xs) ∧
    ∃ time tape, time ≤ 16384 * (xs.length + 1) ^ 2 ∧
      Complexity.runInput binaryMachine time (input a xs) = some (true, tape) ∧
      tape.output = serialize (columns a (0, 0) xs)

private theorem faithful : arena.Law actual := native_binary_row

private theorem zero_fails : ¬ arena.Law zero := by
  intro h
  have hc := (h {Window.zero} [(true, false)]).2.2.1
  norm_num [zero, realize, advance, value, bitsValue, entry, first, last] at hc
  exact Nat.zero_ne_one (congrArg Prod.fst hc)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨{Window.zero}, [], [(true, false)], ?_⟩
  change decode (serialize (columns {Window.zero} (0, 0) [])) ≠
    decode (serialize (columns {Window.zero} (0, 0) [(true, false)]))
  rw [(native_binary_row {Window.zero} []).2.2.1,
    (native_binary_row {Window.zero} [(true, false)]).2.2.1]
  norm_num [advance, value, bitsValue, entry, first, last]

def family : Registration arena (type_of% native_binary_row) where
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
    native_binary_row (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.native_binary_row.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.family
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
    (fun _ a xs => decode (serialize (columns a (0, 0) xs))) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
