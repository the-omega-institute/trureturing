import D5.S3.Arith.Congruence.CarryRevealsLowDigits
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Congruence.CarryRevealsLowDigits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits

@[reducible] def signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => v % p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The full original law; only the outer modulo in the bounded carry formula varies. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ} [hp : Fact p.Prime] (k : ℕ) (x y : ℤ_[p]),
    (∀ n, n ≤ p ^ k - 1 →
      highDigit k (x + ((n : ℕ) : ℤ_[p])) =
        R.readout () p ((PadicInt.toZModPow (k + 1) x).val / p ^ k +
          ((PadicInt.toZModPow (k + 1) x).val % p ^ k + n) / p ^ k)) ∧
    ((PadicInt.toZModPow (k + 1) x).val % p ^ k = 0 →
      ∀ n, 1 ≤ n → n ≤ p ^ k - 1 → highDigit k (x + ((n : ℕ) : ℤ_[p])) = highDigit k x) ∧
    (0 < (PadicInt.toZModPow (k + 1) x).val % p ^ k →
      highDigit k (x + ((p ^ k - (PadicInt.toZModPow (k + 1) x).val % p ^ k : ℕ) : ℤ_[p])) ≠
          highDigit k x ∧
        ∀ n, 1 ≤ n → n < p ^ k - (PadicInt.toZModPow (k + 1) x).val % p ^ k →
          highDigit k (x + ((n : ℕ) : ℤ_[p])) = highDigit k x) ∧
    (digitProtocol k (p ^ k - 1) x = digitProtocol k (p ^ k - 1) y ↔
      PadicInt.toZModPow (k + 1) x = PadicInt.toZModPow (k + 1) y) ∧
    ∀ N, 1 ≤ k → N < p ^ k - 1 →
      digitProtocol k N (0 : ℤ_[p]) = digitProtocol k N (1 : ℤ_[p]) ∧
        PadicInt.toZModPow (k + 1) (0 : ℤ_[p]) ≠ PadicInt.toZModPow (k + 1) (1 : ℤ_[p])

theorem actual_law : arena.Law actual := by
  exact carry_reveals_low_digits

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have impossible := (h (p := 2) 0 0 0).1 0 (by norm_num)
  norm_num [rejected, realize, highDigit] at impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨2, 0, 1, by change (0 : ℕ) % 2 ≠ 1 % 2; norm_num⟩

register_information_theorem carry_reveals_low_digits in arena
  readout via (realize signature (fun _ p v => v % p) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Congruence.CarryRevealsLowDigits
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body",
  "arg"]
      stateOperand := some #["fn", "arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits
