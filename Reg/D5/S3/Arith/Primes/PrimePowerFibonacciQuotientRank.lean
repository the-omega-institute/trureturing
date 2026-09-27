import D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank

open _root_.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
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
  realize signature (fun _ p k => p ^ (k + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p k => p ^ (k + 1) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (p k : ℕ) (_hp : p.Prime) (_hpFive : 5 < p),
    let R := Nat.fib (p ^ (k + 1)) / Nat.fib (p ^ k)
    1 < R ∧ ∀ q : ℕ, q.Prime → q ∣ R →
      fibonacciRank q = r.readout () p k

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood := (prime_power_fibonacci_quotient_rank 7 0 (by decide) (by decide)).2
    13 (by decide) (by decide)
  have hbad := (h 7 0 (by decide) (by decide)).2
    13 (by decide) (by decide)
  change fibonacciRank 13 = 7 ^ (0 + 1) at hgood
  change fibonacciRank 13 = 7 ^ (0 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (p k : ℕ) (_hp : p.Prime) (_hpFive : 5 < p),
      let R := Nat.fib (p ^ (k + 1)) / Nat.fib (p ^ k)
      1 < R ∧ ∀ q : ℕ, q.Prime → q ∣ R →
        fibonacciRank q = p ^ (k + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_power_fibonacci_quotient_rank, rejected, rejected_law⟩
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
    change (7 : ℕ) ^ (0 + 1) ≠ 7 ^ (1 + 1)
    norm_num

register_information_theorem
  _root_.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank.prime_power_fibonacci_quotient_rank
  in arena
  readout via (realize signature (fun _ p k => p ^ (k + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg",
        "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank
