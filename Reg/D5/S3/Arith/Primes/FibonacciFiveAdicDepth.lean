import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciFiveAdicDepth
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth

open _root_.D5.S3.Arith.Primes.FibonacciFiveAdicDepth
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
  realize signature (fun _ _ n => padicValNat 5 (Nat.fib n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 0 < n),
    r.readout () () n = padicValNat 5 n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by decide)
  change 1 = padicValNat 5 1 at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ (n : ℕ) (_hn : 0 < n),
      padicValNat 5 (Nat.fib n) = padicValNat 5 n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_five_adic_depth, rejected, rejected_law⟩
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
    refine ⟨(), (1 : ℕ), (5 : ℕ), ?_⟩
    change padicValNat 5 (Nat.fib 1) ≠ padicValNat 5 (Nat.fib 5)
    norm_num [padicValNat]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => padicValNat 5 (Nat.fib n))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciFiveAdicDepth") "fibonacci_five_adic_depth") "Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth/Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => padicValNat 5 (Nat.fib n))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth
