import Reg.D5.S0.Diagonal.PigeonholeFiber
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber

namespace LeanInformationAuditRegTests.AuricFib.TypedBoundaries
open LeanInformationAudit.Analysis
open LeanInformationAudit.AuricFib.Contract
open Reg.D5.S0.Diagonal.PigeonholeFiber

/-- An unrelated true statement cannot use the native reconstruction constructor. -/
example : True := by
  fail_if_success
    have : NativeSource True.intro := { reconstruction := .exact }
  trivial

/-- Faithful reconstruction does not follow merely from P iff True. -/
example : True := by
  fail_if_success
    have : Reconstruction (type_of% @_root_.D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{0}) True := .exact
  trivial

/-- The reflected source kernel has the two off-diagonal collisions 0↔2. -/
example : threePresentation.kernel () 0 2 = true ∧
    threePresentation.kernel () 0 1 = false := by decide

/-- Finite enumeration counts the complete domain, not its readout image. -/
example : threePresentation.enumeration.states.length = 3 := rfl

/-- A lying kernel has a concrete counterexample before any consumer runs. -/
example : ¬ (∀ left right : Fin 3, true = true ↔
    threeDomain.readout () left = threeDomain.readout () right) := by
  intro h
  have wrong := (h 0 1).1 rfl
  cases wrong

/-- Equality of codes in just one direction is insufficient: an all-equal
kernel fails the required reverse implication on the real source map. -/
example : ¬ (∀ left right : Fin 3, true = true →
    threeDomain.readout () left = threeDomain.readout () right) := by
  intro h
  have wrong := h 0 1 rfl
  cases wrong

/-- Exact value decoding is independent of an otherwise correct kernel. -/
example : ¬ (threePresentation.decode () (.bool true) =
    some (threeDomain.readout () 0)) := by decide

/-- A duplicated row list and an incomplete row list violate different clauses. -/
example : ¬ ([0, 1, 0] : List (Fin 3)).Nodup := by decide
example : ([0, 1] : List (Fin 3)).toFinset ≠ Finset.univ := by decide

/-- Initial capture is retained; both empty and repeated additions collapse. -/
example : threePresentation.layers 0 0 1 = false ∧
    threePresentation.layers 0 = threePresentation.layers 1 ∧
    threePresentation.layers 1 = threePresentation.layers 2 := by decide

/-- A zero-gain source does not need observational dependence or sensitivity. -/
example : ∀ position left right, constantPresentation.layers position left right = true := by decide

/-- The source-indexed plan supplies weak refinement without a strictness claim. -/
example (p : signature.{0}.Params) (n : Nat) : ∀ x y,
    (plan.kernel p (n + 1)).relation x y → (plan.kernel p n).relation x y :=
  plan.refines p n

/-- Scope changes preserve actual readouts while retaining distinct domains. -/
example : quotientPresentation.enumeration.states.length = 2 ∧
    restrictedPresentation.enumeration.states.length = 2 ∧
    threePresentation.enumeration.states.length = 3 := by decide

/-- A quotient merging source values false and true cannot preserve the task. -/
example : ¬ ∃ value : Bool, ∀ x : Fin 3, value = threeDomain.readout () x := by
  rintro ⟨value, all⟩
  have wrong := (all 0).symm.trans (all 1)
  cases wrong

open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.CIRPT

private abbrev threeArena : Arena := Arena.ofFintype (Fin 3)

private def threeCatalog : Catalog threeArena := Catalog.ofVector fun _ : Fin 1 => {
  primitives := {
    Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    atom := fun _ => ⟨.cut, cutKernel threeReading⟩ }
  Statement := True
  proof := True.intro }

/-- Exact counting uses the source-owned complete enumeration and real readout.
The two residual ordered pairs are (0,2) and (2,0), out of six unequal pairs. -/
example : (threeCatalog.fusedCounts threePresentation.enumeration
    (Catalog.finIndexEnumeration 1)).full = 2 := by decide

/-- The existing correctness theorem, not a second counting law, relates this
non-native client's executable count to its actual escape set. -/
example : (threeCatalog.fusedCounts threePresentation.enumeration
    (Catalog.finIndexEnumeration 1)).full = threeCatalog.escapeNumerator threeCatalog.fullIndexSet :=
  Catalog.fusedFull_eq_escapeNumerator _ _ _

/-- Native specialization consumes the indexed original full theorem. -/
example (a : _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) :
    type_of% (_root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution
      false (0, 0) [a]) :=
  NativeSource.specialize
    (occurrence := _root_.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution)
    { reconstruction := .exact } a

open _root_.D5.S3.Arith.FibonacciAtomic
open ImmediateWindowStateCapacity

/-- Both adapter maps commute with the full theorem's actual evaluator. -/
example (a : LiteralWindowEnd.Window) :
    Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.bridge.reader a =
      (rawMachine 0).toDFA.evalFrom
        (some (false, GraftAffineClosure.residue 0 (0, 0))) [a] :=
  NativeBridge.reader_source _ a

example (a : LiteralWindowEnd.Window) :
    Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.bridge.reply a =
      rawOutput ((rawMachine 0).toDFA.evalFrom
        (some (false, GraftAffineClosure.residue 0 (0, 0))) [a, .high]) :=
  NativeBridge.reply_source _ a

/-- A rejected continuation is retained as an actual task output. -/
example :
    Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.bridge.reply .low = none := by
  decide

end LeanInformationAuditRegTests.AuricFib.TypedBoundaries
