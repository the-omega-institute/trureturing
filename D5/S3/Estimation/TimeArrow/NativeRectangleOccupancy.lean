/- GID: D5/S3/Estimation/TimeArrow/NativeRectangleOccupancy
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRectangleOccupancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native cell populations inherit relative second moments and simultaneous occupancy budgets. -/

import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
import D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
noncomputable section

/-- An exact native cell indicator uses the finite relative law, so no
whole-population tail term is needed for a bounded count cell. -/
theorem native_cell_occupancy_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M)) (c : ℕ × ℕ),
          (c.1 : ℝ) ≤ 8 * L → (c.2 : ℝ) ≤ 8 * L →
          ∀ m : ℝ, 0 < m →
          7 / 8 * m ≤ ∑ i ∈ I, rowReference S r L i c →
          (∑ i ∈ I, rowReference S r L i c) ≤ 9 / 8 * m →
          (∑ o : Obs M (2 * M * L) e,
            if ¬(3 / 4 * m ≤ ((I.filter fun i =>
                count e o i 1 = c.1 ∧ count e o i (-1) = c.2).card : ℝ) ∧
              ((I.filter fun i => count e o i 1 = c.1 ∧
                count e o i (-1) = c.2).card : ℝ) ≤ 5 / 4 * m)
            then probability r e S o else 0) ≤
              108 / m + 243 * (A * (L : ℝ) ^ 3 / M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ :=
    native_truncated_weighted_moments κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c hc1 hc2 m hm hlo hhi
  let a : ℝ := ∑ i ∈ I, rowReference S r L i c
  let Z := fun o : Obs M (2 * M * L) e =>
    ((I.filter fun i => count e o i 1 = c.1 ∧ count e o i (-1) = c.2).card : ℝ)
  have hZ (o : Obs M (2 * M * L) e) :
      (∑ i ∈ I, truncatedRow e {c} (fun _ _ => 1) i o) = Z o := by
    simp only [truncatedRow, sum_singleton]
    exact sum_boole _ _
  have hmoment := (h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall
    S e I {c} (fun _ _ => 1)
    (by simpa only [mem_singleton] using fun d (hd : d = c) => hd ▸ And.intro hc1 hc2)
    (by intros; norm_num)).2
  simp only [sum_singleton, one_mul, hZ] at hmoment
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hcomp : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcomp1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hcomp hcomp1 e).2.1.1 S
  have htail := finite_square_markov (probability r e S) Z a (m / 8)
    ((3 / 2) * a + 3 * (A * (L : ℝ) ^ 3 / M) * a ^ 2) hp (by positivity) hmoment
  have hcontain (o : Obs M (2 * M * L) e)
      (ho : ¬(3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m)) : m / 8 < |Z o - a| := by
    by_contra hn
    have hh := abs_le.mp (le_of_not_gt hn)
    apply ho
    dsimp only [a] at hh
    constructor <;> linarith only [hh.1, hh.2, hlo, hhi]
  have hnum : (3 / 2) * a + 3 * (A * (L : ℝ) ^ 3 / M) * a ^ 2 ≤
      (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) * (m / 8) ^ 2 := by
    have ha0 : 0 ≤ a := by dsimp only [a]; linarith only [hlo, hm]
    have hasq : a ^ 2 ≤ (9 / 8 * m) ^ 2 := by dsimp only [a]; nlinarith only [hhi, ha0, hm]
    have hδ : 0 ≤ A * (L : ℝ) ^ 3 / M := by positivity
    have hh := mul_le_mul_of_nonneg_left hasq (show 0 ≤ 3 * (A * (L : ℝ) ^ 3 / M) by positivity)
    have he : (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) * (m / 8) ^ 2 =
        (27 / 16) * m + (243 / 64) * (A * (L : ℝ) ^ 3 / M) * m ^ 2 := by
      field_simp
      <;> ring
    rw [he]
    dsimp only [a] at *
    nlinarith only [hh, hhi]
  apply le_trans _ (htail.trans ((div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < m / 8))).mpr hnum))
  apply sum_le_sum
  intro o _
  change (if ¬(3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m) then _ else _) ≤ _
  by_cases ho : 3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m
  · by_cases ht : m / 8 < |Z o - a| <;> simp [ho, ht, hp o]
  · simp [ho, hcontain o ho]

/-- The four signal cells and background A cell may share arbitrary native
dependence. Only their individual reference means are used in the union bound. -/
theorem native_five_cell_occupancy_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (I : Fin 5 → Finset (Fin M))
          (c : Fin 5 → ℕ × ℕ),
          (∀ j, ((c j).1 : ℝ) ≤ 8 * L ∧ ((c j).2 : ℝ) ≤ 8 * L) →
          ∀ m : ℝ, 0 < m →
          (∀ j, 7 / 8 * m ≤ ∑ i ∈ I j, rowReference S r L i (c j)) →
          (∀ j, (∑ i ∈ I j, rowReference S r L i (c j)) ≤ 9 / 8 * m) →
          (∑ o : Obs M (2 * M * L) e,
            if ¬∀ j, 3 / 4 * m ≤ (((I j).filter fun i =>
                count e o i 1 = (c j).1 ∧ count e o i (-1) = (c j).2).card : ℝ) ∧
              (((I j).filter fun i => count e o i 1 = (c j).1 ∧
                count e o i (-1) = (c j).2).card : ℝ) ≤ 5 / 4 * m
            then probability r e S o else 0) ≤
              540 / m + 1215 * (A * (L : ℝ) ^ 3 / M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_cell_occupancy_budget κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c hc m hm hlo hhi
  let Good := fun (o : Obs M (2 * M * L) e) (j : Fin 5) =>
    3 / 4 * m ≤ (((I j).filter fun i => count e o i 1 = (c j).1 ∧
      count e o i (-1) = (c j).2).card : ℝ) ∧
    (((I j).filter fun i => count e o i 1 = (c j).1 ∧
      count e o i (-1) = (c j).2).card : ℝ) ≤ 5 / 4 * m
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hcomp : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcomp1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hcomp hcomp1 e).2.1.1 S
  calc
    _ ≤ ∑ o : Obs M (2 * M * L) e, ∑ j : Fin 5,
        if ¬Good o j then probability r e S o else 0 := by
      apply sum_le_sum
      intro o _
      change (if ¬∀ j, Good o j then _ else _) ≤ _
      by_cases ho : ∀ j, Good o j
      · simp [ho]
      · obtain ⟨j, hj⟩ := not_forall.mp ho
        simp only [ho, not_false_eq_true, if_true]
        have hh := single_le_sum
          (f := fun j : Fin 5 => if ¬Good o j then probability r e S o else 0)
          (fun k (_ : k ∈ (univ : Finset (Fin 5))) => by
            split_ifs <;> first | exact hp o | exact le_rfl) (mem_univ j)
        simpa only [hj, not_false_eq_true, if_true] using hh
    _ = ∑ j : Fin 5, ∑ o : Obs M (2 * M * L) e,
        if ¬Good o j then probability r e S o else 0 := sum_comm
    _ ≤ ∑ _j : Fin 5, (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) := by
      apply sum_le_sum
      intro j _
      exact h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e (I j) (c j)
        (hc j).1 (hc j).2 m hm (hlo j) (hhi j)
    _ = _ := by simp; ring

/-- Simultaneous occupancy is for the actual four signal cells and the
actual background A cell. Its reference comparison preserves the original
compensation and full population sizes. -/
theorem native_signal_background_occupancy (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ k l : ℕ,
          k = ⌊((1+r)/2)*(L : ℝ)⌋₊ → l = L-k →
          15 ≤ ((1+r)/2)*(L : ℝ) → 30 ≤ ((1-r)/2)*(L : ℝ) →
          let dA := k * Real.log ((1+r)/(1-compensation M q r)) +
            l * Real.log ((1-r)/(1+compensation M q r)) -
            Real.log (((M-q : ℕ) : ℝ)/q)
          Real.log (7/8) ≤ -dA → -dA ≤ Real.log (9/8) →
          let m := (q : ℝ) * rowReference S r L i (k,l)
          let All : Support M M := ⟨univ, by simp⟩
          (∑ o : Obs M (2*M*L) e,
            if ¬((∀ a : Fin 4,
                3/4*m ≤ ((nativeCalibrationCells S e o k l a).card : ℝ) ∧
                ((nativeCalibrationCells S e o k l a).card : ℝ) ≤ 5/4*m) ∧
              3/4*m ≤ ((nativeCalibrationCells All e o k l 0 \ S.val).card : ℝ) ∧
              ((nativeCalibrationCells All e o k l 0 \ S.val).card : ℝ) ≤ 5/4*m)
            then probability r e S o else 0) ≤
              540/m + 1215*(A*(L : ℝ)^3/M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_five_cell_occupancy_budget κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e i j hi hj k l hkfloor hlfloor hplus hminus
  have hr1 : r < 1 := by linarith only [hrκ,hκ]
  have hround := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hround
  rw [← hkfloor, ← hlfloor] at hround
  have hkL : (k : ℝ) ≤ L := by exact_mod_cast hround.1
  have hlL : (l : ℝ) ≤ L := by
    exact_mod_cast (show l ≤ L by rw [hlfloor]; omega)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hk : (k+1 : ℝ) ≤ 8*L := by linarith only [hkL,hLR]
  have hl : (l+1 : ℝ) ≤ 8*L := by linarith only [hlL,hLR]
  dsimp only
  intro hdlo hdhi
  let m := (q : ℝ) * rowReference S r L i (k,l)
  let c : Fin 5 → ℕ × ℕ := ![(k,l),(k+1,l),(k,l+1),(k+1,l+1),(k,l)]
  let I : Fin 5 → Finset (Fin M) := ![S.val,S.val,S.val,S.val,univ \ S.val]
  have hm : 0 < m := mul_pos (by exact_mod_cast (show 0 < q by omega))
    (reference_pos S r κ hκ hr hrκ hcκ hL i (k,l))
  have hsig (a : Fin 4) : (∑ u ∈ S.val,
      rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a)) =
      (q : ℝ) * rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) := by
    calc
      _ = ∑ _u ∈ S.val,
          rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) :=
        sum_congr rfl fun u hu => by simp only [rowReference,b,if_pos hu,if_pos hi]
      _ = _ := by simp [S.property,nsmul_eq_mul]
  have hbg : (∑ u ∈ univ \ S.val, rowReference S r L u (k,l)) =
      ((M-q : ℕ) : ℝ) * rowReference S r L j (k,l) := by
    calc
      _ = ∑ _u ∈ univ \ S.val, rowReference S r L j (k,l) :=
        sum_congr rfl fun u hu => by
          simp only [rowReference,b,if_neg (mem_sdiff.mp hu).2,if_neg hj]
      _ = _ := by simp [card_sdiff_of_subset (subset_univ S.val),S.property,nsmul_eq_mul]
  have hs := floored_signal_four_reference_ratios S r κ hκ hr hrκ hcκ hL i hi hplus hminus
  dsimp only at hs
  rw [← hkfloor, ← hlfloor] at hs
  have hb := background_reference_cell_ratio S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj k l
  have hexlo := Real.exp_le_exp.mpr hdlo
  have hexhi := Real.exp_le_exp.mpr hdhi
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 7/8)] at hexlo
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 9/8)] at hexhi
  have hsm (a : Fin 4) :
      7/8*m ≤ ∑ u ∈ S.val, rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) ∧
      (∑ u ∈ S.val, rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a)) ≤ 9/8*m := by
    rw [hsig a]
    have hh := And.intro
      (mul_le_mul_of_nonneg_left (hs a).1 (by positivity : (0 : ℝ) ≤ q))
      (mul_le_mul_of_nonneg_left (hs a).2 (by positivity : (0 : ℝ) ≤ q))
    simpa [m, mul_assoc, mul_left_comm] using hh
  have hmean (a : Fin 5) : 7/8*m ≤ ∑ u ∈ I a, rowReference S r L u (c a) ∧
      (∑ u ∈ I a, rowReference S r L u (c a)) ≤ 9/8*m := by
    fin_cases a
    · exact hsm 0
    · exact hsm 1
    · exact hsm 2
    · exact hsm 3
    · change 7/8*m ≤ ∑ u ∈ univ \ S.val, rowReference S r L u (k,l) ∧
        (∑ u ∈ univ \ S.val, rowReference S r L u (k,l)) ≤ 9/8*m
      rw [hbg,hb]
      have hh := And.intro (mul_le_mul_of_nonneg_left hexlo hm.le)
        (mul_le_mul_of_nonneg_left hexhi hm.le)
      simpa only [m,mul_comm] using hh
  have he := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c
    (by intro a; fin_cases a <;> simp [c] <;> constructor <;> linarith only [hk,hl])
    m hm (fun a => (hmean a).1) (fun a => (hmean a).2)
  convert he using 1
  apply sum_congr rfl
  intro o _
  congr 1
  have hcell (a : Fin 4) : nativeCalibrationCells S e o k l a =
      S.val.filter fun u => count e o u 1 = k + ![0,1,0,1] a ∧
        count e o u (-1) = l + ![0,0,1,1] a := by
    ext u
    simp [nativeCalibrationCells,native_row_cell_iff]
  have hback : nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val =
      (univ \ S.val).filter fun u => count e o u 1 = k ∧ count e o u (-1) = l := by
    ext u
    simp [nativeCalibrationCells,native_row_cell_iff,and_assoc,and_left_comm,and_comm]
  simp_rw [hcell,hback]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,I,c,m,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Nat.add_zero,and_true]
  apply propext
  tauto

end
end D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
