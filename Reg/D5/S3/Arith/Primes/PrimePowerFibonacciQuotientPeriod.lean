import D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod

open scoped Matrix
open _root_.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod
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
  realize signature (fun _ p k => 4 * p ^ (k + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p k => 4 * p ^ (k + 1) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (p k q : ℕ) (_hp : p.Prime) (_hpFive : 5 < p)
      (_hq : q.Prime)
      (_hqR : q ∣ Nat.fib (p ^ (k + 1)) / Nat.fib (p ^ k)),
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      r.readout () p k

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hdiv : 13 ∣ Nat.fib (7 ^ (0 + 1)) / Nat.fib (7 ^ 0) := by decide
  have hgood := prime_power_fibonacci_quotient_period 7 0 13
    (by decide) (by decide) (by decide) hdiv
  have hbad := h 7 0 13 (by decide) (by decide) (by decide) hdiv
  change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 13)) =
    4 * 7 ^ (0 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (p k q : ℕ) (_hp : p.Prime) (_hpFive : 5 < p)
      (_hq : q.Prime)
      (_hqR : q ∣ Nat.fib (p ^ (k + 1)) / Nat.fib (p ^ k)),
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        4 * p ^ (k + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_power_fibonacci_quotient_period, rejected, rejected_law⟩
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
    change 4 * 7 ^ (0 + 1) ≠ 4 * 7 ^ (1 + 1)
    norm_num

register_information_theorem
  _root_.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod.prime_power_fibonacci_quotient_period
  in arena
  readout via (realize signature (fun _ p k => 4 * p ^ (k + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.PrimePowerFibonacciQuotientPeriod
