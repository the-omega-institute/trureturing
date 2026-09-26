import D5.S3.Arith.GoldenPrimePeriodBounds
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenPrimePeriodBounds

open scoped Matrix
open _root_.D5.S3.Arith.GoldenPrimePeriodBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

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
  realize signature (fun _ _ p => p - 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law readout := ∀ {p : ℕ} (hp : p.Prime) (hpFive : 5 < p),
    (legendreSym 5 p = 1 →
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣
        readout.readout () () p ∧
      ¬ p ∣ orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) ∧
    (legendreSym 5 p = -1 →
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣
        2 * (p + 1) ∧
      ¬ p ∣ orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsplit : legendreSym 5 11 = 1 := by decide
  have hbound := ((h (p := 11) (by decide) (by omega)).1 hsplit).1
  change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 11)) ∣ 1
    at hbound
  have hone := Nat.dvd_one.mp hbound
  have hmatrix := orderOf_eq_one_iff.mp hone
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (ZMod 11) => M 0 1) hmatrix
  norm_num at h01
  exact (by decide : (1 : ZMod 11) ≠ 0) h01

def registration : Registration arena
    (∀ {p : ℕ} (hp : p.Prime) (hpFive : 5 < p),
      (legendreSym 5 p = 1 →
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣ p - 1 ∧
        ¬ p ∣ orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) ∧
      (legendreSym 5 p = -1 →
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣ 2 * (p + 1) ∧
        ¬ p ∣ orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_prime_period_bounds, rejected, rejected_law⟩
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
    refine ⟨(), (7 : ℕ), (11 : ℕ), ?_⟩
    change (7 : ℕ) - 1 ≠ 11 - 1
    decide

register_information_theorem _root_.D5.S3.Arith.GoldenPrimePeriodBounds.golden_prime_period_bounds
  in arena
  readout via (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.GoldenPrimePeriodBounds
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn",
        "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.GoldenPrimePeriodBounds
