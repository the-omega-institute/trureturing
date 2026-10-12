/- GID: D5/S3/Estimation/TimeArrow/NativeRectangleOccupancy
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRectangleOccupancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native cell populations inherit relative second moments and simultaneous occupancy budgets. -/

import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets

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

end
end D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
