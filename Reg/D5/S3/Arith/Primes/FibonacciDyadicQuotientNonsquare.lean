import D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare

open _root_.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
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
  realize signature (fun _ _ k => Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (k : ℕ) (_hk : 1 ≤ k),
    let q := r.readout () () k
    (k = 1 → q % 5 = 3) ∧ (2 ≤ k → q % 5 = 2) ∧ ¬ IsSquare q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 (by decide)).1 rfl
  change (Nat.fib (2 ^ (1 + 1)) / Nat.fib (2 ^ 1) + 1) % 5 = 3 at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ (k : ℕ) (_hk : 1 ≤ k),
      let q := Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k)
      (k = 1 → q % 5 = 3) ∧ (2 ≤ k → q % 5 = 2) ∧ ¬ IsSquare q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_dyadic_quotient_nonsquare, rejected, rejected_law⟩
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
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change Nat.fib (2 ^ (1 + 1)) / Nat.fib (2 ^ 1) ≠
      Nat.fib (2 ^ (2 + 1)) / Nat.fib (2 ^ 2)
    norm_num

register_information_theorem
  _root_.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare
  in arena
  readout via (realize signature
    (fun _ _ k => Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
