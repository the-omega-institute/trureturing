import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare

open _root_.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
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
      (_hclass : q % 120 = 49 ∨ q % 120 = 71),
    0 < r.readout () q k ∧
      (r.readout () q k) % 31 = (if k % 2 = 0 then 27 else 23) ∧
      ¬ IsSquare (r.readout () q k)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 71 0 (by decide) (by decide) (by decide)).2.1
  norm_num [rejected, realize] at hbad

def registration : Registration arena
    (∀ (q k : ℕ) (_hq : q.Prime) (_hqge : 7 ≤ q)
      (_hclass : q % 120 = 49 ∨ q % 120 = 71),
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
        (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)) % 31 =
          (if k % 2 = 0 then 27 else 23) ∧
        ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro q k hq hqge hclass
    exact fibonacci_prime_power_mod31_nonsquare q k hq hqge hclass,
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
    refine ⟨2, (0 : ℕ), (1 : ℕ), ?_⟩
    change Nat.fib (2 ^ (0 + 1)) / Nat.fib (2 ^ 0) ≠
      Nat.fib (2 ^ (1 + 1)) / Nat.fib (2 ^ 1)
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciPrimePowerMod31Nonsquare") "fibonacci_prime_power_mod31_nonsquare") "Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare/Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
