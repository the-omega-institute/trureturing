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

namespace Exposed_serialize_length

abbrev signature : Signature where
  Params := Unit
  State _ := List Column
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ xs => (serialize xs).length) (fun e => nomatch e)
def alternate : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ xs : List Column, R.readout () () xs = 2 * xs.length

private theorem faithful : arena.Law actual := by intro xs; exact serialize_length xs
private theorem alternate_fails : ¬ arena.Law alternate := by intro h; have hc := h [(false, false)]; norm_num [realize, alternate] at hc
private theorem dependence : ObservationalDependence signature actual := by intro role; exact ⟨(), [], [(false, false)], by simp [actual, realize, serialize]⟩

def family : Registration arena (type_of% serialize_length) where
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
    serialize_length (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.serialize_length.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.Exposed_serialize_length.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ xs => (serialize xs).length) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    stateOperand := none
                    booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Exposed_serialize_length

namespace Exposed_parse_serialize

abbrev signature : Signature where
  Params := Unit
  State _ := List Column
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Column
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ xs => parse (serialize xs)) (fun e => nomatch e)
def alternate : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ xs : List Column, R.readout () () xs = xs

private theorem faithful : arena.Law actual := by intro xs; exact parse_serialize xs
private theorem alternate_fails : ¬ arena.Law alternate := by intro h; have hc := h [(false, false)]; simp [realize, alternate] at hc
private theorem dependence : ObservationalDependence signature actual := by intro role; exact ⟨(), [], [(false, false)], by simp [actual, realize, parse_serialize]⟩

def family : Registration arena (type_of% parse_serialize) where
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
    parse_serialize (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.parse_serialize.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.Exposed_parse_serialize.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ xs => parse (serialize xs)) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    stateOperand := none
                    booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Exposed_parse_serialize

namespace Exposed_columns_length

abbrev signature : Signature where
  Params := Σ _ : Finset Window, Carry
  State _ := List Column
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p xs => (columns p.1 p.2 xs).length) (fun e => nomatch e)
def alternate : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a : Finset Window) (c : Carry) (xs : List Column), R.readout () ⟨a, c⟩ xs = xs.length + 3

private theorem faithful : arena.Law actual := by intro a c xs; exact columns_length a c xs
private theorem alternate_fails : ¬ arena.Law alternate := by intro h; have hc := h ∅ (0, 0) []; norm_num [realize, alternate] at hc
private theorem dependence : ObservationalDependence signature actual := by intro role; exact ⟨⟨∅, (0, 0)⟩, [], [(false, false)], by simp [actual, realize, columns_length]⟩

def family : Registration arena (type_of% columns_length) where
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
    columns_length (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.columns_length.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.Exposed_columns_length.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ p xs => (columns p.1 p.2 xs).length) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"]
                    stateBinder := 2
                    functionOperand := false
                    stateOperand := none
                    booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Exposed_columns_length

namespace Exposed_exec_program

abbrev signature : Signature where
  Params := Finset Window
  State _ := List Column
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ xs => 8 * xs.length + 28) (fun e => nomatch e)
def alternate : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a : Finset Window) (xs : List Column), Complexity.StackProgram.Exec program program.start (registers (input a xs) []) (R.readout () a xs) (true, registers (serialize (columns a (0, 0) xs)) [])

private theorem faithful : arena.Law actual := by intro a xs; exact exec_program a xs
private theorem alternate_fails : ¬ arena.Law alternate := by intro h; have hc := (h ∅ []).run; change Complexity.StackProgram.run program 0 _ _ = _ at hc; simp only [Complexity.StackProgram.run] at hc; contradiction
private theorem dependence : ObservationalDependence signature actual := by intro role; exact ⟨∅, [], [(false, false)], by norm_num [actual, realize]⟩

def family : Registration arena (type_of% exec_program) where
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
    exec_program (Realization signature) Type Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.exec_program.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow.Exposed_exec_program.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature (fun _ _ xs => 8 * xs.length + 28) (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg"]
                    stateBinder := 1
                    functionOperand := false
                    stateOperand := none
                    booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Exposed_exec_program

end Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryRow
