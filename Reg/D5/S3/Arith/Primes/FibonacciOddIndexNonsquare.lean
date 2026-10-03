import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare

open _root_.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => Nat.fib m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (m : ℕ), 3 ≤ m → Odd m → ¬ IsSquare (r.readout () () m)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 3 (by decide) (by decide)
  exact hb ⟨1, rfl⟩

def registration : Registration arena
    (∀ (m : ℕ), 3 ≤ m → Odd m → ¬ IsSquare (Nat.fib m)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro m hm hodd
    exact fibonacci_odd_index_nonsquare m hm hodd,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (1 : ℕ), (3 : ℕ), ?_⟩
    change Nat.fib 1 ≠ Nat.fib 3
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare.fibonacci_odd_index_nonsquare) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ m => Nat.fib m) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciOddIndexNonsquare") "fibonacci_odd_index_nonsquare") "Reg.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare/Reg.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ m => Nat.fib m) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciOddIndexNonsquare, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
