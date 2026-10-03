import D5.S3.Arith.GoldenFibonacciModulusPeriod
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod

open scoped Matrix
open _root_.D5.S3.Arith.GoldenFibonacciModulusPeriod
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
  realize signature (fun _ _ n => 4 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => 4 * n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 5 ≤ n) (_hodd : Odd n),
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib n))) =
      r.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 5 (by decide) (by decide)
  have hgood := golden_fibonacci_modulus_period 5 (by decide) (by decide)
  change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib 5))) =
    4 * 5 + 1 at hbad
  omega

def registration : Registration arena
    (∀ (n : ℕ) (_hn : 5 ≤ n) (_hodd : Odd n),
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib n))) =
        4 * n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_fibonacci_modulus_period, rejected, rejected_law⟩
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
    cases i
    refine ⟨(), (5 : ℕ), (7 : ℕ), ?_⟩
    change (20 : ℕ) ≠ 28
    decide

register_information_theorem
  _root_.D5.S3.Arith.GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period
  in arena
  readout via (realize signature (fun _ _ n => 4 * n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.GoldenFibonacciModulusPeriod
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod
