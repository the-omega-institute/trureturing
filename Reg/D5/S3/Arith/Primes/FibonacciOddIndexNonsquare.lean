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

register_information_theorem
  fibonacci_odd_index_nonsquare
  in arena
  readout via (realize signature (fun _ _ m => Nat.fib m) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
