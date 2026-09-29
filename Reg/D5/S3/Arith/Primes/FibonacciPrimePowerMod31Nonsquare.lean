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

register_information_theorem
  fibonacci_prime_power_mod31_nonsquare
  in arena
  readout via (realize signature
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
