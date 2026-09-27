import D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod

open scoped Matrix
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

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
  realize signature
    (fun _ p a =>
      let τ := orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      τ * p ^ (a - h))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p a =>
      let τ := orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      τ * p ^ (a - h) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (p a : ℕ) (_hp : p.Prime) (_hpFive : 5 < p) (_ha : 1 ≤ a),
    let τ := orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
    let h := padicValNat p (Nat.fib (fibonacciRank p))
    0 < h ∧
      padicValNat p (Nat.fib τ) = h ∧
      padicValNat p (Nat.fib τ) = padicValNat p (Nat.fib (τ - 1) - 1) ∧
      orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) =
        r.readout () p a

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let τ7 := orderOf
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 7))
  let h7 := padicValNat 7 (Nat.fib (fibonacciRank 7))
  have hgood := (golden_matrix_prime_power_period 7 1
    (by decide) (by decide) (by decide)).2.2.2
  have hbad := (h 7 1 (by decide) (by decide) (by decide)).2.2.2
  change orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (7 ^ 1))) =
    τ7 * 7 ^ (1 - h7) at hgood
  change orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (7 ^ 1))) =
    τ7 * 7 ^ (1 - h7) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (p a : ℕ) (_hp : p.Prime) (_hpFive : 5 < p) (_ha : 1 ≤ a),
      let τ := orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      0 < h ∧
        padicValNat p (Nat.fib τ) = h ∧
        padicValNat p (Nat.fib τ) = padicValNat p (Nat.fib (τ - 1) - 1) ∧
        orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) =
          τ * p ^ (a - h)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_matrix_prime_power_period, rejected, rejected_law⟩
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
    let h7 := padicValNat 7 (Nat.fib (fibonacciRank 7))
    let τ7 := orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 7))
    have hunit : IsUnit
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 7)) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      simp [Matrix.det_fin_two_of]
    have htpos : 0 < τ7 := hunit.isOfFinOrder.orderOf_pos
    refine ⟨7, h7 + 1, h7 + 2, ?_⟩
    change τ7 * 7 ^ (h7 + 1 - h7) ≠ τ7 * 7 ^ (h7 + 2 - h7)
    have hfirst : h7 + 1 - h7 = 1 := by omega
    have hsecond : h7 + 2 - h7 = 2 := by omega
    rw [hfirst, hsecond]
    intro heq
    norm_num at heq
    omega

register_information_theorem
  _root_.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period
  in arena
  readout via (realize signature
    (fun _ p a =>
      let τ := orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      τ * p ^ (a - h))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end
end Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
