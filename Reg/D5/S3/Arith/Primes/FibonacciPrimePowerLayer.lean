import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciPrimePowerLayer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciPrimePowerLayer
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
  realize signature (fun _ q s => Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (q s : ℕ) (_hq : q.Prime) (_hq5 : q ≠ 5) (_hs : 1 ≤ s)
    (_hexclude : ¬ (q = 2 ∧ s = 1)),
    let C := r.readout () q s
    1 < C ∧ Nat.Coprime C (Nat.fib (q ^ (s - 1))) ∧ ¬ IsSquare C ∧
      (∀ p : ℕ, p.Prime → p ∣ C →
        fibonacciRank p = q ^ s ∧ p ≠ q ∧
          padicValNat p C = padicValNat p (Nat.fib (fibonacciRank p))) ∧
      (∃ p : ℕ, p.Prime ∧ p ∣ C ∧
        Odd (padicValNat p (Nat.fib (fibonacciRank p))))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 3 1 (by decide) (by decide) (by decide) (by decide)).1
  change 1 < 1 at hb
  exact Nat.lt_irrefl 1 hb

def registration : Registration arena
    (∀ (q s : ℕ) (_hq : q.Prime) (_hq5 : q ≠ 5) (_hs : 1 ≤ s)
      (_hexclude : ¬ (q = 2 ∧ s = 1)),
      let C := Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1))
      1 < C ∧ Nat.Coprime C (Nat.fib (q ^ (s - 1))) ∧ ¬ IsSquare C ∧
        (∀ p : ℕ, p.Prime → p ∣ C →
          fibonacciRank p = q ^ s ∧ p ≠ q ∧
            padicValNat p C = padicValNat p (Nat.fib (fibonacciRank p))) ∧
        (∃ p : ℕ, p.Prime ∧ p ∣ C ∧
          Odd (padicValNat p (Nat.fib (fibonacciRank p))))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_prime_power_layer, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), ?_⟩
    change Nat.fib (3 ^ 1) / Nat.fib (3 ^ (1 - 1)) ≠
      Nat.fib (3 ^ 2) / Nat.fib (3 ^ (2 - 1))
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.fibonacci_prime_power_layer) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q s => Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1))) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciPrimePowerLayer") "fibonacci_prime_power_layer") "Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer/Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ q s => Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1))) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "value"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer
