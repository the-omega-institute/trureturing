import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => Nat.fib n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (p n : ℕ) (_hp : p.Prime) (_hpn : p ∣ Nat.fib n)
    (_hpIndex : ¬p ∣ n),
    padicValNat p (r.readout () p n) = padicValNat p (Nat.fib (fibonacciRank p))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood := fibonacci_original_rank_valuation 2 3 (by decide) (by decide) (by decide)
  have hbad := h 2 3 (by decide) (by decide) (by decide)
  change padicValNat 2 0 = padicValNat 2 (Nat.fib (fibonacciRank 2)) at hbad
  rw [← hgood] at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ (p n : ℕ) (_hp : p.Prime) (_hpn : p ∣ Nat.fib n)
      (_hpIndex : ¬p ∣ n),
      padicValNat p (Nat.fib n) = padicValNat p (Nat.fib (fibonacciRank p))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_original_rank_valuation, rejected, rejected_law⟩
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
    refine ⟨2, (0 : ℕ), (3 : ℕ), ?_⟩
    change Nat.fib 0 ≠ Nat.fib 3
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation.fibonacci_original_rank_valuation) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => Nat.fib n)
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciPrimeToIndexValuation") "fibonacci_original_rank_valuation") "Reg.D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation/Reg.D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => Nat.fib n)
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
