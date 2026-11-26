/- GID: D5/S3/Quantum/Dynamics/NativeReader/Carrier
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Carrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal legal-path carriers and ready interfaces for the native auxiliary reader. -/

import D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
import D5.S3.Quantum.Measurement.OneSidedGoldenHistory
import D5.S1.Words.AdmissibleWords.AdmissibleCount

/-! The source's occupation bits, including every legal path outside its code interface. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Dynamics.NativeReader

open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.Measurement.OneSidedGoldenHistory (x x_properties)

/-- The Fibonacci fusion adjacency, in the literal occupation-bit convention. -/
def adjacent (a b : Bool) : Prop := ¬ (a = true ∧ b = true)

instance : DecidableRel adjacent := fun _ _ => inferInstanceAs (Decidable (¬ (_ ∧ _)))

theorem adjacent_symm : Std.Symm adjacent := ⟨by
  intro a b h hab
  exact h hab.symm⟩

/-- The original source: sites zero through ten; the fixed exterior is 1, then 1,0. -/
abbrev Source := LegalPath adjacent 10 false false

/-- The entire extended carrier: sites zero through fourteen; exterior 1 and 1,0. -/
abbrev Extended := LegalPath adjacent 14 false false

/-- Original source sectors retain every legal source path. -/
def SourceSector (i : Bool) := {q : Source // q.1 9 = i}

instance (i : Bool) : Fintype (SourceSector i) := by
  classical
  unfold SourceSector
  infer_instance

/-- Indices zero and six are the actual b9 and b15; the five intervening bits are z. -/
abbrev Tail (i : Bool) := LegalPath adjacent 6 i true

instance (i : Bool) : DecidableEq (Tail i) := Classical.decEq _
instance : DecidableEq Source := Classical.decEq _
instance : DecidableEq Extended := Classical.decEq _

/-- The single actual ready tail, including its two boundary bits. -/
def readyTail (i : Bool) : Tail i :=
  ⟨![i, false, true, false, false, false, true], by
    refine ⟨by simp, by simp, ?_⟩
    intro k
    fin_cases k <;> simp [adjacent]⟩

/-- The original J(e00100,0), with the original tail b10,b11,b12=010 understood. -/
def readySource : Source :=
  ⟨![false, false, false, true, false, false, false, true, false, false, false], by
    refine ⟨by simp, by simp, ?_⟩
    intro k
    fin_cases k <;> decide⟩

/-- The actual report reads the original physical address thirteen. -/
def report {i : Bool} (z : Tail i) : Bool := z.1 4

/-- Homogeneous Perron weights give exactly the source Q, with no basis change. -/
def weight : Bool → ℝ
  | false => 1
  | true => x

theorem weight_positive (b : Bool) : 0 < weight b := by
  cases b <;> simp [weight, x_properties.1]

theorem weight_perron (a : Bool) :
    (∑ b : Bool with adjacent a b, weight b) = Real.goldenRatio * weight a := by
  have hadd : 1 + x = Real.goldenRatio := by
    rw [x, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hmul : Real.goldenRatio * x = 1 :=
    mul_inv_cancel₀ Real.goldenRatio_ne_zero
  cases a
  · simpa [Finset.sum_filter, Fintype.sum_bool, adjacent, weight, add_comm] using hadd
  · simpa [Finset.sum_filter, Fintype.sum_bool, adjacent, weight] using hmul.symm

/-- Recursive admissibility agrees with the pointwise no-adjacent-ones condition. -/
theorem adm_iff_adjacent (n : ℕ) (w : Fin n → Bool) :
    Adm n w ↔ ∀ k : Fin (n - 1),
      adjacent (w ⟨k, by omega⟩) (w ⟨k + 1, by omega⟩) := by
  induction n with
  | zero => simp [Adm]
  | succ n ih =>
    cases n with
    | zero => simp [Adm]
    | succ m =>
      rw [adm_two_iff, ih]
      constructor
      · rintro ⟨h0, ht⟩ k
        by_cases hk : k.val = 0
        · simpa [adjacent, hk] using h0
        · have h := ht ⟨k.val - 1, by omega⟩
          simpa [Fin.tail, Fin.succ, Nat.sub_add_cancel (by omega : 1 ≤ k.val)] using h
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [adjacent] using h ⟨0, by omega⟩
        · intro k
          simpa [Fin.tail, Fin.succ, Nat.add_assoc] using h ⟨k.val + 1, by omega⟩

/-- Padding by the two fixed zeros is a bijection, retaining every internal bit. -/
def pathWordEquiv (n : ℕ) :
    LegalPath adjacent (n + 1) false false ≃ {w : Fin n → Bool // Adm n w} where
  toFun q := ⟨fun k => q.1 ⟨k.val + 1, by omega⟩, by
    rw [adm_iff_adjacent]
    intro k
    exact q.2.2.2 ⟨k.val + 1, by omega⟩⟩
  invFun w := ⟨fun k => if h : 0 < k.val ∧ k.val < n + 1 then
      w.1 ⟨k.val - 1, by omega⟩ else false, by
    refine ⟨by simp, ?_, ?_⟩
    · simp
    · intro k
      by_cases hk : k.val = 0
      · simp [hk, adjacent]
      by_cases hlast : k.val + 1 = n + 1
      · simp [hlast, adjacent]
      · have hw := (adm_iff_adjacent n w.1).mp w.2 ⟨k.val - 1, by omega⟩
        simpa [Fin.val_castSucc, Fin.val_succ, hk, hlast,
          show 0 < k.val by omega, show k.val < n + 1 by omega,
          show k.val + 1 < n + 1 by omega,
          Nat.sub_add_cancel (by omega : 1 ≤ k.val)] using hw⟩
  left_inv q := by
    apply Subtype.ext
    funext k
    dsimp
    split_ifs with h
    · have he : (⟨k.val - 1 + 1, by omega⟩ : Fin (n + 1 + 1)) = k :=
        Fin.ext (by change k.val - 1 + 1 = k.val; omega)
      exact congrArg q.1 he
    · by_cases hk : k.val = 0
      · have he : k = 0 := Fin.ext hk
        simpa [he] using q.2.1.symm
      · have he : k = Fin.last (n + 1) := Fin.ext (by simp; omega)
        simpa [he] using q.2.2.1.symm
  right_inv w := by
    apply Subtype.ext
    funext k
    simp

theorem source_card : Fintype.card Source = 89 := by
  rw [Fintype.card_congr (pathWordEquiv 9), admissibleWord_card_eq_fib]
  decide

theorem extended_card : Fintype.card Extended = 610 := by
  rw [Fintype.card_congr (pathWordEquiv 13), admissibleWord_card_eq_fib]
  decide

end D5.S3.Quantum.Dynamics.NativeReader
