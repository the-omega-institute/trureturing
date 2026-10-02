import D5.S3.Arith.Primes.FibSquareclassRigidity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibSquareclassRigidity

open _root_.D5.S3.Arith.Primes.FibSquareclassRigidity
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
  realize signature (fun _ m n => Nat.fib m * Nat.fib n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n),
    IsSquare (r.readout () m n) ↔
      m = n ∨
      ((m = 1 ∨ m = 2 ∨ m = 12) ∧ (n = 1 ∨ n = 2 ∨ n = 12)) ∨
      ((m = 3 ∨ m = 6) ∧ (n = 3 ∨ n = 6))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : IsSquare (rejected.readout () 1 4) := ⟨0, rfl⟩
  have hb := (h 1 4 (by decide) (by decide)).mp hs
  norm_num at hb

def registration : Registration arena
    (∀ (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n),
      IsSquare (Nat.fib m * Nat.fib n) ↔
        m = n ∨
        ((m = 1 ∨ m = 2 ∨ m = 12) ∧ (n = 1 ∨ n = 2 ∨ n = 12)) ∨
        ((m = 3 ∨ m = 6) ∧ (n = 3 ∨ n = 6))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_squareclass_pairs, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, (1 : ℕ), (3 : ℕ), ?_⟩
    change Nat.fib 1 * Nat.fib 1 ≠ Nat.fib 1 * Nat.fib 3
    decide

register_information_theorem
  fibonacci_squareclass_pairs
  in arena
  readout via (realize signature (fun _ m n => Nat.fib m * Nat.fib n)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibSquareclassRigidity
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibSquareclassRigidity
