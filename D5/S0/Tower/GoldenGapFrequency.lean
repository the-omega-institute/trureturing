/- GID: D5/S0/Tower/GoldenGapFrequency
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenGapFrequency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full golden tower gaps have exact Fibonacci multiplicities and limiting frequency. -/

import D5.S0.Tower.GoldenSubstitution
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

namespace D5.S0.Tower.GoldenGapFrequency

open Filter Topology
open D5.S0.Conventions
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenSubstitution

local notation "φ" => Real.goldenRatio

private theorem level_card_pos (Q : ℕ) : 0 < Nat.fib (Q + 2) := by
  exact Nat.fib_pos.2 (by omega)

/-- The adjacent gap after an indexed name, completed by the boundary gap to one. -/
noncomputable def fullGap (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) : ℝ :=
  if h : i.1 + 1 < Nat.fib (Q + 2) then
    indexedNameValue Q ⟨i.1 + 1, h⟩ - indexedNameValue Q i
  else
    1 - indexedNameValue Q i

/-- The number of full level-`Q` gaps having the larger frozen length. -/
noncomputable def largeGapCount (Q : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (Nat.fib (Q + 2)))).filter fun i =>
    fullGap Q i = φ ^ (-(Q : ℤ))).card

/-- The number of full level-`Q` gaps having the smaller frozen length. -/
noncomputable def smallGapCount (Q : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (Nat.fib (Q + 2)))).filter fun i =>
    fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ))).card

private def lastIndex (Q : ℕ) : Fin (Nat.fib (Q + 2)) :=
  ⟨Nat.fib (Q + 2) - 1, Nat.sub_lt (level_card_pos Q) (by omega)⟩

private noncomputable def terminalGap (Q : ℕ) : ℝ :=
  1 - indexedNameValue Q (lastIndex Q)

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

private theorem last_wdigits_add_two (Q : ℕ) :
    wdigits (Nat.fib (Q + 4) - 1) =
      (Q + 3) :: wdigits (Nat.fib (Q + 2) - 1) := by
  symm
  apply wdigits_unique
  · rw [List.IsZeckendorfRep, List.cons_append]
    have hlast : Nat.fib (Q + 2) - 1 < Nat.fib (Q + 2) :=
      Nat.sub_lt (level_card_pos Q) (by omega)
    let i : Fin (Nat.fib (Q + 2)) := ⟨Nat.fib (Q + 2) - 1, hlast⟩
    apply (goldenNameEquiv Q i).1.2.cons
    intro k hk
    have hk_mem := List.mem_of_mem_head? hk
    rw [List.mem_append, List.mem_singleton] at hk_mem
    rcases hk_mem with hk_digits | rfl
    · have := (goldenNameEquiv Q i).2 k hk_digits
      omega
    · omega
  · simp only [List.map_cons, List.sum_cons, decode_wdigits]
    have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
      rw [Nat.fib_add_two (n := Q + 2), add_comm]
    rw [hrec]
    have := level_card_pos Q
    omega

private theorem zpow_shift_two (Q : ℕ) :
    φ ^ (-(Q : ℤ)) * φ ^ (-2 : ℤ) = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
  rw [← zpow_add₀ Real.goldenRatio_ne_zero]
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

private theorem indexed_last_add_two (Q : ℕ) :
    indexedNameValue (Q + 2) (lastIndex (Q + 2)) =
      φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q (lastIndex Q) := by
  change
    ((wdigits (Nat.fib (Q + 4) - 1)).map fun k : ℕ ↦
        φ ^ ((k : ℤ) - ((Q + 4 : ℕ) : ℤ))).sum =
      φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) *
        ((wdigits (Nat.fib (Q + 2) - 1)).map fun k : ℕ ↦
          φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum
  rw [last_wdigits_add_two]
  simp only [List.map_cons, List.sum_cons]
  have hhead : ((Q + 3 : ℕ) : ℤ) - ((Q + 4 : ℕ) : ℤ) = -1 := by
    push_cast
    omega
  rw [hhead]
  congr 1
  induction wdigits (Nat.fib (Q + 2) - 1) with
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

private theorem terminal_gap_add_two (Q : ℕ) :
    terminalGap (Q + 2) = terminalGap Q * φ ^ (-2 : ℤ) := by
  rw [terminalGap, indexed_last_add_two]
  unfold terminalGap
  calc
    1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q (lastIndex Q)) =
        (1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ))) +
          (1 - indexedNameValue Q (lastIndex Q)) * φ ^ (-2 : ℤ) := by ring
    _ = (1 - indexedNameValue Q (lastIndex Q)) * φ ^ (-2 : ℤ) := by
      rw [inverse_sum]
      ring

private theorem terminal_gap_spectrum : ∀ Q : ℕ,
    terminalGap Q = φ ^ (-(Q : ℤ)) ∨
      terminalGap Q = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  apply Nat.twoStepInduction
  · left
    norm_num [terminalGap, lastIndex, indexedNameValue_zero]
  · right
    have hlast : lastIndex 1 = ⟨1, by norm_num [Nat.fib]⟩ := by
      apply Fin.ext
      norm_num [lastIndex, Nat.fib]
    rw [terminalGap, hlast, indexedNameValue_one]
    change 1 - φ ^ (-1 : ℤ) = φ ^ (-2 : ℤ)
    linarith [inverse_sum]
  · intro Q hQ _hQ1
    rw [terminal_gap_add_two]
    rcases hQ with hlarge | hsmall
    · left
      rw [hlarge, zpow_shift_two]
    · right
      rw [hsmall]
      simpa [Nat.add_assoc] using zpow_shift_two (Q + 1)

private theorem refined_internal_gap_type (Q : ℕ) (hQ : 2 ≤ Q)
    (i : Fin (Nat.fib (Q + 2) - 1)) :
    (indexedNameValue Q
            ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
          indexedNameValue Q
            ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
        φ ^ (-(Q : ℤ)) ∧
      ∃ j : Fin (Nat.fib (Q + 3)), insertedNameIndices Q i = {j}) ∨
    (indexedNameValue Q
            ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
          indexedNameValue Q
            ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
        φ ^ (-((Q + 1 : ℕ) : ℤ)) ∧
      insertedNameIndices Q i = ∅) := by
  rcases consecutive_nameValue_gap Q i with hlarge | hsmall
  · left
    rcases (golden_gap_substitution Q hQ i).2 hlarge with
      ⟨j, hinserted, _hleft, _hright⟩
    exact ⟨hlarge, j, hinserted⟩
  · right
    exact ⟨hsmall, (golden_gap_substitution Q hQ i).1 hsmall |>.1⟩

private theorem fullGap_spectrum (Q : ℕ) (hQ : 2 ≤ Q)
    (i : Fin (Nat.fib (Q + 2))) :
    fullGap Q i = φ ^ (-(Q : ℤ)) ∨
      fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  by_cases hnext : i.1 + 1 < Nat.fib (Q + 2)
  · let j : Fin (Nat.fib (Q + 2) - 1) := ⟨i.1, by omega⟩
    rcases refined_internal_gap_type Q hQ j with hlarge | hsmall
    · left
      simpa [fullGap, hnext, j] using hlarge.1
    · right
      simpa [fullGap, hnext, j] using hsmall.1
  · have hilast : i = lastIndex Q := by
      apply Fin.ext
      dsimp [lastIndex]
      have := i.2
      omega
    rw [fullGap, dif_neg hnext, hilast]
    exact terminal_gap_spectrum Q

private theorem small_gap_lt_large_gap (Q : ℕ) :
    φ ^ (-((Q + 1 : ℕ) : ℤ)) < φ ^ (-(Q : ℤ)) := by
  exact zpow_lt_zpow_right₀ Real.one_lt_goldenRatio (by push_cast; omega)

private theorem not_large_iff_small (Q : ℕ) (hQ : 2 ≤ Q)
    (i : Fin (Nat.fib (Q + 2))) :
    (¬fullGap Q i = φ ^ (-(Q : ℤ))) ↔
      fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  constructor
  · intro hnot
    rcases fullGap_spectrum Q hQ i with hlarge | hsmall
    · exact (hnot hlarge).elim
    · exact hsmall
  · intro hsmall hlarge
    exact (small_gap_lt_large_gap Q).ne (hsmall.symm.trans hlarge)

private theorem fullGap_count_total (Q : ℕ) (hQ : 2 ≤ Q) :
    largeGapCount Q + smallGapCount Q = Nat.fib (Q + 2) := by
  classical
  let gaps : Finset (Fin (Nat.fib (Q + 2))) := Finset.univ
  let isLarge := fun i : Fin (Nat.fib (Q + 2)) ↦ fullGap Q i = φ ^ (-(Q : ℤ))
  let isSmall := fun i : Fin (Nat.fib (Q + 2)) ↦
    fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ))
  have hcomplement : gaps.filter (fun i ↦ ¬isLarge i) = gaps.filter isSmall := by
    ext i
    simp only [Finset.mem_filter]
    rw [not_large_iff_small Q hQ i]
  change (gaps.filter isLarge).card + (gaps.filter isSmall).card = _
  rw [← hcomplement, Finset.card_filter_add_card_filter_not]
  simp [gaps]

private theorem sum_fullGap (Q : ℕ) :
    ∑ i : Fin (Nat.fib (Q + 2)), fullGap Q i = 1 := by
  classical
  let n := Nat.fib (Q + 2)
  have hn : 0 < n := level_card_pos Q
  have hcard : n - 1 + 1 = n := by omega
  let e : Fin (n - 1 + 1) ≃ Fin n := finCongr hcard
  have hinternal (i : Fin (n - 1)) :
      fullGap Q (e i.castSucc) =
        indexedNameValue Q ⟨i.1 + 1, by dsimp [n] at i ⊢; omega⟩ -
          indexedNameValue Q ⟨i.1, by dsimp [n] at i ⊢; omega⟩ := by
    rw [fullGap, dif_pos]
    · congr 2
    · dsimp [e, n]
      omega
  have hterminal : fullGap Q (e (Fin.last (n - 1))) = terminalGap Q := by
    have heq : e (Fin.last (n - 1)) = lastIndex Q := by
      apply Fin.ext
      dsimp [e, lastIndex, n]
    rw [heq, fullGap, dif_neg, terminalGap]
    dsimp [lastIndex]
    omega
  let v : ℕ → ℝ := fun k ↦
    if h : k < n then indexedNameValue Q ⟨k, by simpa [n] using h⟩ else 0
  have hinternal_sum :
      (∑ i : Fin (n - 1),
          (indexedNameValue Q ⟨i.1 + 1, by dsimp [n] at i ⊢; omega⟩ -
            indexedNameValue Q ⟨i.1, by dsimp [n] at i ⊢; omega⟩)) =
        indexedNameValue Q (lastIndex Q) := by
    calc
      (∑ i : Fin (n - 1),
          (indexedNameValue Q ⟨i.1 + 1, by dsimp [n] at i ⊢; omega⟩ -
            indexedNameValue Q ⟨i.1, by dsimp [n] at i ⊢; omega⟩)) =
          ∑ i : Fin (n - 1), (v (i.1 + 1) - v i.1) := by
            apply Fintype.sum_congr
            intro i
            simp [v, show i.1 < n by omega, show i.1 + 1 < n by omega]
      _ = ∑ i ∈ Finset.range (n - 1), (v (i + 1) - v i) :=
        Fin.sum_univ_eq_sum_range (fun i ↦ v (i + 1) - v i) (n - 1)
      _ = v (n - 1) - v 0 := Finset.sum_range_sub v (n - 1)
      _ = indexedNameValue Q (lastIndex Q) := by
        simp [v, hn, lastIndex, n, indexedNameValue_zero]
  calc
    (∑ i : Fin n, fullGap Q i) = ∑ i : Fin (n - 1 + 1), fullGap Q (e i) :=
      (Equiv.sum_comp e (fullGap Q)).symm
    _ = (∑ i : Fin (n - 1), fullGap Q (e i.castSucc)) +
        fullGap Q (e (Fin.last (n - 1))) := Fin.sum_univ_castSucc _
    _ = indexedNameValue Q (lastIndex Q) + terminalGap Q := by
      rw [hterminal]
      simp_rw [hinternal]
      rw [hinternal_sum]
    _ = 1 := by simp [terminalGap]

private theorem sum_fullGap_by_type (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ i : Fin (Nat.fib (Q + 2)), fullGap Q i) =
      (largeGapCount Q : ℝ) * φ ^ (-(Q : ℤ)) +
        (smallGapCount Q : ℝ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  classical
  let gaps : Finset (Fin (Nat.fib (Q + 2))) := Finset.univ
  let isLarge := fun i : Fin (Nat.fib (Q + 2)) ↦ fullGap Q i = φ ^ (-(Q : ℤ))
  let isSmall := fun i : Fin (Nat.fib (Q + 2)) ↦
    fullGap Q i = φ ^ (-((Q + 1 : ℕ) : ℤ))
  have hcomplement : gaps.filter (fun i ↦ ¬isLarge i) = gaps.filter isSmall := by
    ext i
    simp only [Finset.mem_filter]
    rw [not_large_iff_small Q hQ i]
  have hlarge :
      (∑ i ∈ gaps.filter isLarge, fullGap Q i) =
        (gaps.filter isLarge).card * φ ^ (-(Q : ℤ)) := by
    calc
      (∑ i ∈ gaps.filter isLarge, fullGap Q i) =
          ∑ _i ∈ gaps.filter isLarge, φ ^ (-(Q : ℤ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (Finset.mem_filter.1 hi).2
      _ = (gaps.filter isLarge).card * φ ^ (-(Q : ℤ)) := by simp
  have hsmall :
      (∑ i ∈ gaps.filter isSmall, fullGap Q i) =
        (gaps.filter isSmall).card * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
    calc
      (∑ i ∈ gaps.filter isSmall, fullGap Q i) =
          ∑ _i ∈ gaps.filter isSmall, φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (Finset.mem_filter.1 hi).2
      _ = (gaps.filter isSmall).card * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by simp
  calc
    (∑ i : Fin (Nat.fib (Q + 2)), fullGap Q i) = ∑ i ∈ gaps, fullGap Q i := by
      simp [gaps]
    _ = (∑ i ∈ gaps.filter isLarge, fullGap Q i) +
        ∑ i ∈ gaps.filter (fun i ↦ ¬isLarge i), fullGap Q i := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = (∑ i ∈ gaps.filter isLarge, fullGap Q i) +
        ∑ i ∈ gaps.filter isSmall, fullGap Q i := by rw [hcomplement]
    _ = (largeGapCount Q : ℝ) * φ ^ (-(Q : ℤ)) +
        (smallGapCount Q : ℝ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
      rw [hlarge, hsmall]
      rfl

private theorem fib_gap_sum (Q : ℕ) :
    (Nat.fib (Q + 1) : ℝ) * φ ^ (-(Q : ℤ)) +
        (Nat.fib Q : ℝ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) = 1 := by
  have hshift : φ ^ (-(Q : ℤ)) = φ * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
    calc
      φ ^ (-(Q : ℤ)) = φ ^ ((1 : ℤ) + -((Q + 1 : ℕ) : ℤ)) := by
        congr 1
        push_cast
        omega
      _ = φ ^ (1 : ℤ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) :=
        zpow_add₀ Real.goldenRatio_ne_zero _ _
      _ = φ * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by norm_num
  calc
    (Nat.fib (Q + 1) : ℝ) * φ ^ (-(Q : ℤ)) +
        (Nat.fib Q : ℝ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) =
      (φ * (Nat.fib (Q + 1) : ℝ) + Nat.fib Q) *
        φ ^ (-((Q + 1 : ℕ) : ℤ)) := by rw [hshift]; ring
    _ = φ ^ (Q + 1) * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
      rw [Real.goldenRatio_mul_fib_succ_add_fib]
    _ = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ Real.goldenRatio_ne_zero]
      norm_num

/-- Full level-`Q` gaps have exact Fibonacci multiplicities, including the boundary gap. -/
theorem golden_full_gap_counts (Q : ℕ) (hQ : 2 ≤ Q) :
    largeGapCount Q = Nat.fib (Q + 1) ∧
    smallGapCount Q = Nat.fib Q ∧
    largeGapCount Q + smallGapCount Q = Fintype.card (GoldenName Q) := by
  have htotal := fullGap_count_total Q hQ
  have hfibTotal : Nat.fib (Q + 1) + Nat.fib Q = Nat.fib (Q + 2) := by
    rw [Nat.fib_add_two (n := Q), add_comm]
  have htotalCast :
      (largeGapCount Q : ℝ) + smallGapCount Q =
        (Nat.fib (Q + 1) : ℝ) + Nat.fib Q := by
    exact_mod_cast htotal.trans hfibTotal.symm
  have hweighted :
      (largeGapCount Q : ℝ) * φ ^ (-(Q : ℤ)) +
          (smallGapCount Q : ℝ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) = 1 := by
    rw [← sum_fullGap_by_type Q hQ, sum_fullGap]
  have hcountDiff :
      (smallGapCount Q : ℝ) - Nat.fib Q =
        -((largeGapCount Q : ℝ) - Nat.fib (Q + 1)) := by
    linarith
  have hweightedDiff :
      ((largeGapCount Q : ℝ) - Nat.fib (Q + 1)) * φ ^ (-(Q : ℤ)) +
          ((smallGapCount Q : ℝ) - Nat.fib Q) *
            φ ^ (-((Q + 1 : ℕ) : ℤ)) = 0 := by
    nlinarith [fib_gap_sum Q]
  have hproduct :
      ((largeGapCount Q : ℝ) - Nat.fib (Q + 1)) *
          (φ ^ (-(Q : ℤ)) - φ ^ (-((Q + 1 : ℕ) : ℤ))) = 0 := by
    calc
      ((largeGapCount Q : ℝ) - Nat.fib (Q + 1)) *
          (φ ^ (-(Q : ℤ)) - φ ^ (-((Q + 1 : ℕ) : ℤ))) =
        ((largeGapCount Q : ℝ) - Nat.fib (Q + 1)) * φ ^ (-(Q : ℤ)) +
          ((smallGapCount Q : ℝ) - Nat.fib Q) *
            φ ^ (-((Q + 1 : ℕ) : ℤ)) := by rw [hcountDiff]; ring
      _ = 0 := hweightedDiff
  have hlengths :
      φ ^ (-(Q : ℤ)) ≠ φ ^ (-((Q + 1 : ℕ) : ℤ)) :=
    (small_gap_lt_large_gap Q).ne'
  have hlargeCast : (largeGapCount Q : ℝ) = Nat.fib (Q + 1) := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hproduct).resolve_right (sub_ne_zero.mpr hlengths)
  have hlarge : largeGapCount Q = Nat.fib (Q + 1) := by
    exact_mod_cast hlargeCast
  have hsmall : smallGapCount Q = Nat.fib Q := by omega
  refine ⟨hlarge, hsmall, ?_⟩
  rw [hlarge, hsmall, golden_name_card]
  exact hfibTotal

/-- The ratio of large to small full-gap frequencies tends to the golden ratio. -/
theorem golden_gap_frequency_ratio :
    Filter.Tendsto
      (fun Q : ℕ => (largeGapCount (Q + 2) : ℝ) / smallGapCount (Q + 2))
      Filter.atTop (nhds φ) := by
  have hrewrite :
      (fun Q : ℕ => (largeGapCount (Q + 2) : ℝ) / smallGapCount (Q + 2)) =
        fun Q : ℕ => (Nat.fib (Q + 3) : ℝ) / Nat.fib (Q + 2) := by
    funext Q
    rw [(golden_full_gap_counts (Q + 2) (by omega)).1,
      (golden_full_gap_counts (Q + 2) (by omega)).2.1]
  rw [hrewrite]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (tendsto_add_atTop_iff_nat
      (f := fun Q : ℕ => (Nat.fib (Q + 1) : ℝ) / Nat.fib Q)
      (l := nhds φ) 2).2 tendsto_fib_succ_div_fib_atTop

end D5.S0.Tower.GoldenGapFrequency
