/- GID: D5/S0/Tower/GoldenGapWord
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenGapWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The full golden gap word is the Fibonacci substitution word. -/

import D5.S0.Tower.GoldenGapFrequency
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace D5.S0.Tower.GoldenGapWord

open D5.S0.Conventions
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenGapFrequency

local notation "φ" => Real.goldenRatio

/-- The oriented Fibonacci replacement: large becomes large-small and small becomes large. -/
def subst : Bool → List Bool
  | true => [true, false]
  | false => [true]

/-- The finite Fibonacci word obtained by iterating the oriented replacement from one large gap. -/
def fibWord : ℕ → List Bool
  | 0 => [true]
  | Q + 1 => (fibWord Q).flatMap subst

/-- Every boundary-completed level-`Q` gap, in its frozen `Fin` order, classified as large. -/
noncomputable def goldenGapWord (Q : ℕ) : List Bool :=
  List.ofFn fun i : Fin (Nat.fib (Q + 2)) =>
    if fullGap Q i = φ ^ (-(Q : ℤ)) then true else false

private theorem level_card_pos (Q : ℕ) : 0 < Nat.fib (Q + 2) := by
  exact Nat.fib_pos.2 (by omega)

private theorem zpow_shift_one_left (Q : ℕ) :
    φ ^ (-1 : ℤ) * φ ^ (-(Q : ℤ)) = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  rw [mul_comm, ← zpow_add₀ Real.goldenRatio_ne_zero]
  congr 1
  push_cast
  omega

private theorem zpow_shift_two_left (Q : ℕ) :
    φ ^ (-2 : ℤ) * φ ^ (-(Q : ℤ)) = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
  rw [mul_comm, ← zpow_add₀ Real.goldenRatio_ne_zero]
  congr 1
  push_cast
  omega

private theorem inverse_sum : φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) = 1 := by
  have hne := Real.goldenRatio_ne_zero
  calc
    φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) =
        φ ^ (-2 : ℤ) * φ + φ ^ (-2 : ℤ) := by
      rw [show (-1 : ℤ) = -2 + 1 by omega, zpow_add₀ hne]
      norm_num only [zpow_ofNat, pow_one]
    _ = φ ^ (-2 : ℤ) * (φ + 1) := by ring
    _ = φ ^ (-2 : ℤ) * φ ^ 2 := by rw [Real.goldenRatio_sq]
    _ = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hne]
      norm_num

private theorem indexedNameValue_zero (Q : ℕ) :
    indexedNameValue Q ⟨0, level_card_pos Q⟩ = 0 := by
  change ((wdigits 0).map fun k : ℕ ↦
    φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum = 0
  rw [show wdigits 0 = [] by
    symm
    apply wdigits_unique
    · exact List.IsZeckendorfRep_nil
    · rfl]
  rfl

private theorem indexedNameValue_one (Q : ℕ) (h : 1 < Nat.fib (Q + 2)) :
    indexedNameValue Q ⟨1, h⟩ = φ ^ (-(Q : ℤ)) := by
  change ((wdigits 1).map fun k : ℕ ↦
    φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum = _
  rw [show wdigits 1 = [2] by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  push_cast
  omega

private theorem indexedNameValue_lower (Q : ℕ) (i : Fin (Nat.fib (Q + 4)))
    (hi : i.1 < Nat.fib (Q + 3)) :
    indexedNameValue (Q + 2) i =
      φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨i.1, hi⟩ := by
  change ((wdigits i.1).map fun k : ℕ ↦
      φ ^ ((k : ℤ) - ((Q + 4 : ℕ) : ℤ))).sum =
    φ ^ (-1 : ℤ) *
      ((wdigits i.1).map fun k : ℕ ↦
        φ ^ ((k : ℤ) - ((Q + 3 : ℕ) : ℤ))).sum
  induction wdigits i.1 with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexponent :
          (k : ℤ) - ((Q + 4 : ℕ) : ℤ) =
            -1 + ((k : ℤ) - ((Q + 3 : ℕ) : ℤ)) := by
        push_cast
        omega
      rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
      ring

private theorem wdigits_fib_add (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) :
    wdigits (Nat.fib (Q + 3) + j.1) = (Q + 3) :: wdigits j.1 := by
  symm
  apply wdigits_unique
  · rw [List.IsZeckendorfRep, List.cons_append]
    apply (goldenNameEquiv Q j).1.2.cons
    intro k hk
    have hk_mem := List.mem_of_mem_head? hk
    rw [List.mem_append, List.mem_singleton] at hk_mem
    rcases hk_mem with hk_digits | rfl
    · have := (goldenNameEquiv Q j).2 k hk_digits
      omega
    · omega
  · change Nat.fib (Q + 3) + ((wdigits j.1).map Nat.fib).sum =
      Nat.fib (Q + 3) + j.1
    rw [decode_wdigits]

private theorem indexedNameValue_upper (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) :
    indexedNameValue (Q + 2)
        ⟨Nat.fib (Q + 3) + j.1, by
          rw [show Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) by
            rw [Nat.fib_add_two (n := Q + 2), add_comm]]
          omega⟩ =
      φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q j := by
  change ((wdigits (Nat.fib (Q + 3) + j.1)).map fun k : ℕ ↦
      φ ^ ((k : ℤ) - ((Q + 4 : ℕ) : ℤ))).sum = _
  rw [wdigits_fib_add]
  simp only [List.map_cons, List.sum_cons]
  have hhead : ((Q + 3 : ℕ) : ℤ) - ((Q + 4 : ℕ) : ℤ) = -1 := by
    push_cast
    omega
  rw [hhead]
  congr 1
  change ((wdigits j.1).map fun k : ℕ ↦
      φ ^ ((k : ℤ) - ((Q + 4 : ℕ) : ℤ))).sum =
    φ ^ (-2 : ℤ) *
      ((wdigits j.1).map fun k : ℕ ↦
        φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum
  induction wdigits j.1 with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexponent :
          (k : ℤ) - ((Q + 4 : ℕ) : ℤ) =
            -2 + ((k : ℤ) - ((Q + 2 : ℕ) : ℤ)) := by
        push_cast
        omega
      rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
      ring

private def lowerIndex (Q : ℕ) (i : Fin (Nat.fib (Q + 3))) :
    Fin (Nat.fib (Q + 4)) :=
  ⟨i.1, by
    rw [show Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) by
      rw [Nat.fib_add_two (n := Q + 2), add_comm]]
    have := level_card_pos Q
    omega⟩

private def upperIndex (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    Fin (Nat.fib (Q + 4)) :=
  ⟨Nat.fib (Q + 3) + i.1, by
    rw [show Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) by
      rw [Nat.fib_add_two (n := Q + 2), add_comm]]
    omega⟩

private theorem fullGap_lower (Q : ℕ) (i : Fin (Nat.fib (Q + 3))) :
    fullGap (Q + 2) (lowerIndex Q i) = φ ^ (-1 : ℤ) * fullGap (Q + 1) i := by
  have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
    rw [Nat.fib_add_two (n := Q + 2), add_comm]
  have hfine : (lowerIndex Q i).1 + 1 < Nat.fib (Q + 4) := by
    dsimp [lowerIndex]
    rw [hrec]
    have := level_card_pos Q
    omega
  by_cases hnext : i.1 + 1 < Nat.fib (Q + 3)
  · rw [fullGap, dif_pos hfine, fullGap, dif_pos hnext]
    change
      indexedNameValue (Q + 2) ⟨i.1 + 1, hfine⟩ -
          indexedNameValue (Q + 2) ⟨i.1, (lowerIndex Q i).2⟩ =
        φ ^ (-1 : ℤ) *
          (indexedNameValue (Q + 1) ⟨i.1 + 1, hnext⟩ - indexedNameValue (Q + 1) i)
    rw [indexedNameValue_lower Q ⟨i.1 + 1, hfine⟩ hnext,
      indexedNameValue_lower Q ⟨i.1, (lowerIndex Q i).2⟩ i.2]
    ring
  · have hboundary : Nat.fib (Q + 3) ≤ i.1 + 1 := Nat.le_of_not_gt hnext
    have heq : i.1 + 1 = Nat.fib (Q + 3) := by omega
    rw [fullGap, dif_pos hfine, fullGap, dif_neg hnext]
    change
      indexedNameValue (Q + 2) ⟨i.1 + 1, hfine⟩ -
          indexedNameValue (Q + 2) ⟨i.1, (lowerIndex Q i).2⟩ =
        φ ^ (-1 : ℤ) * (1 - indexedNameValue (Q + 1) i)
    rw [indexedNameValue_lower Q ⟨i.1, (lowerIndex Q i).2⟩ i.2]
    have hright :
        (⟨i.1 + 1, hfine⟩ : Fin (Nat.fib (Q + 4))) = upperIndex Q ⟨0, level_card_pos Q⟩ := by
      apply Fin.ext
      simp [upperIndex, heq]
    rw [hright]
    change
      indexedNameValue (Q + 2)
          ⟨Nat.fib (Q + 3) + (0 : ℕ), by
            rw [hrec]
            exact Nat.add_lt_add_left (level_card_pos Q) _⟩ -
          φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) i =
        φ ^ (-1 : ℤ) * (1 - indexedNameValue (Q + 1) i)
    rw [indexedNameValue_upper Q ⟨0, level_card_pos Q⟩, indexedNameValue_zero]
    ring

private theorem fullGap_upper (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    fullGap (Q + 2) (upperIndex Q i) = φ ^ (-2 : ℤ) * fullGap Q i := by
  have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
    rw [Nat.fib_add_two (n := Q + 2), add_comm]
  by_cases hnext : i.1 + 1 < Nat.fib (Q + 2)
  · have hfine : (upperIndex Q i).1 + 1 < Nat.fib (Q + 4) := by
      dsimp [upperIndex]
      rw [hrec]
      omega
    rw [fullGap, dif_pos hfine, fullGap, dif_pos hnext]
    have hright :
        (⟨(upperIndex Q i).1 + 1, hfine⟩ : Fin (Nat.fib (Q + 4))) =
          upperIndex Q ⟨i.1 + 1, hnext⟩ := by
      apply Fin.ext
      rfl
    rw [hright]
    change
      indexedNameValue (Q + 2)
          ⟨Nat.fib (Q + 3) + (i.1 + 1), by rw [hrec]; omega⟩ -
          indexedNameValue (Q + 2)
            ⟨Nat.fib (Q + 3) + i.1, by rw [hrec]; omega⟩ =
        φ ^ (-2 : ℤ) *
          (indexedNameValue Q ⟨i.1 + 1, hnext⟩ - indexedNameValue Q i)
    rw [indexedNameValue_upper Q ⟨i.1 + 1, hnext⟩, indexedNameValue_upper Q i]
    ring
  · have hfine : ¬(upperIndex Q i).1 + 1 < Nat.fib (Q + 4) := by
      dsimp [upperIndex]
      rw [hrec]
      omega
    rw [fullGap, dif_neg hfine, fullGap, dif_neg hnext]
    change
      1 - indexedNameValue (Q + 2)
          ⟨Nat.fib (Q + 3) + i.1, by rw [hrec]; omega⟩ =
        φ ^ (-2 : ℤ) * (1 - indexedNameValue Q i)
    rw [indexedNameValue_upper]
    calc
      1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q i) =
          (1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ))) +
            φ ^ (-2 : ℤ) * (1 - indexedNameValue Q i) := by ring
      _ = φ ^ (-2 : ℤ) * (1 - indexedNameValue Q i) := by rw [inverse_sum]; ring

private theorem fullGap_lower_large_iff (Q : ℕ) (i : Fin (Nat.fib (Q + 3))) :
    fullGap (Q + 2) (lowerIndex Q i) = φ ^ (-((Q + 2 : ℕ) : ℤ)) ↔
      fullGap (Q + 1) i = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  rw [fullGap_lower, ← zpow_shift_one_left (Q + 1)]
  constructor <;> intro h
  · nlinarith [zpow_pos Real.goldenRatio_pos (-1 : ℤ)]
  · rw [h]

private theorem fullGap_upper_large_iff (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    fullGap (Q + 2) (upperIndex Q i) = φ ^ (-((Q + 2 : ℕ) : ℤ)) ↔
      fullGap Q i = φ ^ (-(Q : ℤ)) := by
  rw [fullGap_upper, ← zpow_shift_two_left Q]
  constructor <;> intro h
  · nlinarith [zpow_pos Real.goldenRatio_pos (-2 : ℤ)]
  · rw [h]

private def lastIndex (Q : ℕ) : Fin (Nat.fib (Q + 2)) :=
  ⟨Nat.fib (Q + 2) - 1, Nat.sub_lt (level_card_pos Q) (by omega)⟩

private theorem upperIndex_lastIndex (Q : ℕ) :
    upperIndex Q (lastIndex Q) = lastIndex (Q + 2) := by
  apply Fin.ext
  dsimp [upperIndex, lastIndex]
  rw [show Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) by
    rw [Nat.fib_add_two (n := Q + 2), add_comm]]
  have := level_card_pos Q
  omega

private theorem terminal_fullGap_spectrum : ∀ Q : ℕ,
    fullGap Q (lastIndex Q) = φ ^ (-(Q : ℤ)) ∨
      fullGap Q (lastIndex Q) = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  apply Nat.twoStepInduction
  · left
    have hlast : lastIndex 0 = ⟨0, by norm_num [Nat.fib]⟩ := by
      apply Fin.ext
      norm_num [lastIndex, Nat.fib]
    rw [hlast, fullGap, dif_neg, indexedNameValue_zero]
    · norm_num
    · norm_num [Nat.fib]
  · right
    have hlast : lastIndex 1 = ⟨1, by norm_num [Nat.fib]⟩ := by
      apply Fin.ext
      norm_num [lastIndex, Nat.fib]
    rw [hlast, fullGap, dif_neg, indexedNameValue_one]
    · change 1 - φ ^ (-1 : ℤ) = φ ^ (-2 : ℤ)
      linarith [inverse_sum]
    · norm_num [Nat.fib]
  · intro Q hQ _hQ1
    rw [← upperIndex_lastIndex Q, fullGap_upper]
    rcases hQ with hlarge | hsmall
    · left
      rw [hlarge, zpow_shift_two_left]
    · right
      rw [hsmall]
      simpa [Nat.add_assoc] using zpow_shift_two_left (Q + 1)

private theorem fullGap_spectrum (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    fullGap Q i = φ ^ (-(Q : ℤ)) ∨
      fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  by_cases hnext : i.1 + 1 < Nat.fib (Q + 2)
  · let j : Fin (Nat.fib (Q + 2) - 1) := ⟨i.1, by omega⟩
    rcases consecutive_nameValue_gap Q j with hlarge | hsmall
    · left
      simpa [fullGap, hnext, j] using hlarge
    · right
      simpa [fullGap, hnext, j] using hsmall
  · have hilast : i = lastIndex Q := by
      apply Fin.ext
      dsimp [lastIndex]
      have := i.2
      omega
    rw [hilast]
    exact terminal_fullGap_spectrum Q

private theorem small_gap_lt_large_gap (Q : ℕ) :
    φ ^ (-((Q + 1 : ℕ) : ℤ)) < φ ^ (-(Q : ℤ)) := by
  exact zpow_lt_zpow_right₀ Real.one_lt_goldenRatio (by push_cast; omega)

/-- A false letter is exactly the small frozen length, not an unclassified third length. -/
theorem golden_gap_false_iff_small (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    (if fullGap Q i = φ ^ (-(Q : ℤ)) then true else false) = false ↔
      fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  by_cases hlarge : fullGap Q i = φ ^ (-(Q : ℤ))
  · have hsmall : ¬fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
      intro h
      exact (small_gap_lt_large_gap Q).ne (h.symm.trans hlarge)
    constructor
    · intro h
      simp only [hlarge, ↓reduceIte, Bool.true_eq_false] at h
    · intro h
      exact (hsmall h).elim
  · rcases fullGap_spectrum Q i with h | hsmall
    · exact (hlarge h).elim
    · constructor
      · intro _
        exact hsmall
      · intro _
        simp only [hlarge, ↓reduceIte]

private theorem goldenGapWord_add_two (Q : ℕ) :
    goldenGapWord (Q + 2) = goldenGapWord (Q + 1) ++ goldenGapWord Q := by
  have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
    rw [Nat.fib_add_two (n := Q + 2), add_comm]
  unfold goldenGapWord
  rw [List.ofFn_congr hrec]
  rw [← List.ofFn_fin_append]
  rw [List.ofFn_inj]
  funext i
  refine Fin.addCases (m := Nat.fib (Q + 3)) (n := Nat.fib (Q + 2)) ?_ ?_ i
  · intro j
    have hindex :
        Fin.cast hrec.symm (Fin.castAdd (Nat.fib (Q + 2)) j) = lowerIndex Q j := by
      apply Fin.ext
      rfl
    rw [Fin.append_left, hindex]
    exact if_congr (fullGap_lower_large_iff Q j) rfl rfl
  · intro j
    have hindex :
        Fin.cast hrec.symm (Fin.natAdd (Nat.fib (Q + 3)) j) = upperIndex Q j := by
      apply Fin.ext
      rfl
    rw [Fin.append_right, hindex]
    exact if_congr (fullGap_upper_large_iff Q j) rfl rfl

private theorem goldenGapWord_zero : goldenGapWord 0 = [true] := by
  have hgap (i : Fin (Nat.fib (0 + 2))) : fullGap 0 i = φ ^ (-(0 : ℤ)) := by
    have hi : i = ⟨0, by norm_num [Nat.fib]⟩ := by
      apply Fin.ext
      change i.1 = 0
      have hcard : Nat.fib (0 + 2) = 1 := by norm_num [Nat.fib]
      have hi' := (Fin.cast hcard i).2
      change i.1 < 1 at hi'
      omega
    rw [hi, fullGap, dif_neg, indexedNameValue_zero]
    · norm_num
    · norm_num [Nat.fib]
  rw [goldenGapWord]
  change [if fullGap 0 ⟨0, by norm_num [Nat.fib]⟩ = φ ^ (-(0 : ℤ)) then true else false] =
    [true]
  rw [hgap]
  simp

private theorem goldenGapWord_one : goldenGapWord 1 = [true, false] := by
  have hzero :
      fullGap 1 (⟨0, by norm_num [Nat.fib]⟩ : Fin (Nat.fib (1 + 2))) =
        φ ^ (-(1 : ℤ)) := by
    rw [fullGap, dif_pos, indexedNameValue_one, indexedNameValue_zero]
    · change φ ^ (-1 : ℤ) - 0 = φ ^ (-1 : ℤ)
      ring
    · norm_num [Nat.fib]
  have hone :
      fullGap 1 (⟨1, by norm_num [Nat.fib]⟩ : Fin (Nat.fib (1 + 2))) =
        φ ^ (-2 : ℤ) := by
    rw [fullGap, dif_neg, indexedNameValue_one]
    · change 1 - φ ^ (-1 : ℤ) = φ ^ (-2 : ℤ)
      linarith [inverse_sum]
    · norm_num [Nat.fib]
  have hne : φ ^ (-2 : ℤ) ≠ φ ^ (-(1 : ℤ)) :=
    (small_gap_lt_large_gap 1).ne
  rw [goldenGapWord]
  change
    [if fullGap 1 ⟨0, by norm_num [Nat.fib]⟩ = φ ^ (-(1 : ℤ)) then true else false,
      if fullGap 1 ⟨1, by norm_num [Nat.fib]⟩ = φ ^ (-(1 : ℤ)) then true else false] =
      [true, false]
  rw [hzero, hone]
  simp only [if_pos, hne, if_false]

private theorem fibWord_add_two (Q : ℕ) : fibWord (Q + 2) = fibWord (Q + 1) ++ fibWord Q := by
  induction Q with
  | zero => decide
  | succ Q ih =>
      change
        (fibWord (Q + 2)).flatMap subst =
          (fibWord (Q + 1)).flatMap subst ++ (fibWord Q).flatMap subst
      rw [ih, List.flatMap_append]

private theorem goldenGapWord_eq_fibWord : ∀ Q : ℕ, goldenGapWord Q = fibWord Q := by
  apply Nat.twoStepInduction
  · simpa [fibWord] using goldenGapWord_zero
  · simpa [fibWord, subst] using goldenGapWord_one
  · intro Q hQ hQ1
    rw [goldenGapWord_add_two, fibWord_add_two, hQ1, hQ]

/-- The complete golden tower gap word is the Fibonacci substitution word. -/
theorem golden_full_gap_word (Q : ℕ) (_hQ : 2 ≤ Q) : goldenGapWord Q = fibWord Q :=
  goldenGapWord_eq_fibWord Q

/-- One refinement substitutes every full gap in order, including the terminal boundary gap. -/
theorem golden_gap_word_step (Q : ℕ) (hQ : 2 ≤ Q) :
    (goldenGapWord Q).flatMap subst = goldenGapWord (Q + 1) := by
  rw [golden_full_gap_word Q hQ, golden_full_gap_word (Q + 1) (by omega)]
  rfl

end D5.S0.Tower.GoldenGapWord
