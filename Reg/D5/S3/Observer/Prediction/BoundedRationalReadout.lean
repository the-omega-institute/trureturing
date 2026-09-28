import D5.S3.Observer.Prediction.BoundedRationalReadout
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Prediction.BoundedRationalReadout

open _root_.D5.S3.Observer.Prediction.BoundedRationalReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => balanceBits (balance w)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)

noncomputable def arena : Arena where
  signature := signature
  Law R :=
    ∀ (K : ℕ) (_hK : 1 ≤ K) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1 / 4)
    (_hδ : tailError K ≤ ε),
    (∀ b : ℤ, exactReadout (-b) = 1 - exactReadout b) ∧
    (∀ b : ℤ, (K : ℤ) ≤ b →
      3 / 4 - exactReadout b = 1 / (2 * (1 + (3 : ℝ) ^ b)) ∧
      0 ≤ 3 / 4 - exactReadout b ∧ 3 / 4 - exactReadout b ≤ tailError K) ∧
    (∀ b : ℤ, b ≤ -(K : ℤ) →
      exactReadout b - 1 / 4 = 1 / (2 * (1 + (3 : ℝ) ^ (-b))) ∧
      0 ≤ exactReadout b - 1 / 4 ∧ exactReadout b - 1 / 4 ≤ tailError K) ∧
    (∀ w : List Bool, |clippedReadout K (balance w) - exactReadout (balance w)| ≤ ε) ∧
    (∀ b : ℤ, 0 < (outputFraction K b).2 ∧
      ((outputFraction K b).1 : ℝ) / (outputFraction K b).2 = clippedReadout K b ∧
      (outputFraction K b).1.bits.length ≤ 2 * K + 4 ∧
      (outputFraction K b).2.bits.length ≤ 2 * K + 4) ∧
    (∀ i : Fin (2 * K - 1),
      0 < (interiorTable K i).2 ∧
      ((interiorTable K i).1 : ℝ) / (interiorTable K i).2 =
        exactReadout ((i.val : ℤ) - ((K : ℤ) - 1)) ∧
      (interiorTable K i).1 < 2 ^ (2 * K + 4) ∧
      (interiorTable K i).2 < 2 ^ (2 * K + 4)) ∧
    tableBits K ≤ 24 * K ^ 2 ∧
    balance [] = 0 ∧
    (∀ (w : List Bool) (x : Bool),
      balance (w ++ [x]) = balance w + (if x then 1 else -1)) ∧
    (∀ w : List Bool,
      balance w = (w.count true : ℤ) - w.count false ∧
      (balance w).natAbs ≤ w.length ∧
      R.readout () () w ≤ 2 + Nat.log2 (w.length + 1)) ∧
    (¬ ∃ forecast : ℕ → ℝ → ℕ → ℝ, ∀ (w : List Bool) (n : ℕ),
      |forecast w.length (clippedReadout K (balance w)) n -
        exactReadout (balance w - (n : ℤ))| ≤ ε) ∧
    ¬ ∃ update : ℝ → Bool → ℝ, ∀ (b : ℤ) (x : Bool),
      update (clippedReadout K b) x =
        clippedReadout K (b + (if x then 1 else -1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 le_rfl (1 / 8) (by norm_num) (by norm_num)
    (by norm_num [tailError])).2.2.2.2.2.2.2.2.2.1 []
  have hn : ¬ (100 : ℕ) ≤ 2 + Nat.log2 1 := by decide
  exact hn hh.2.2

noncomputable def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_tail_clip_error_and_bit_budget, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), [], [true], ?_⟩
    change (1 : ℕ) ≠ 2
    decide

register_information_theorem uniform_tail_clip_error_and_bit_budget in arena
  readout via (realize signature (fun _ _ w => balanceBits (balance w))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Prediction.BoundedRationalReadout
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Observer.Prediction.BoundedRationalReadout
