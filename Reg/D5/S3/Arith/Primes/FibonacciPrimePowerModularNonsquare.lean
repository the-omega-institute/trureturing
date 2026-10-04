import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare

open _root_.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
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
  realize signature (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (q k : ℕ) (_hq : q.Prime) (_hqge : 7 ≤ q)
      (_h1 : q % 120 ≠ 1) (_h49 : q % 120 ≠ 49)
      (_h71 : q % 120 ≠ 71) (_h119 : q % 120 ≠ 119),
    0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      ¬ IsSquare (r.readout () q k)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 7 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).2
  apply hbad
  change IsSquare (1 : ℕ)
  exact ⟨1, by norm_num⟩

def registration : Registration arena
    (∀ (q k : ℕ) (_hq : q.Prime) (_hqge : 7 ≤ q)
      (_h1 : q % 120 ≠ 1) (_h49 : q % 120 ≠ 49)
      (_h71 : q % 120 ≠ 71) (_h119 : q % 120 ≠ 119),
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
        ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro q k hq hqge h1 h49 h71 h119
    exact fibonacci_prime_power_modular_nonsquare q k hq hqge h1 h49 h71 h119,
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
    refine ⟨7, (0 : ℕ), (1 : ℕ), ?_⟩
    change Nat.fib (7 ^ (0 + 1)) / Nat.fib (7 ^ 0) ≠
      Nat.fib (7 ^ (1 + 1)) / Nat.fib (7 ^ 1)
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciPrimePowerModularNonsquare") "fibonacci_prime_power_modular_nonsquare") "Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare/Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
