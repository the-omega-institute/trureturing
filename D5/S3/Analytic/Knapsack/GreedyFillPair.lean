/- GID: D5/S3/Analytic/Knapsack/GreedyFillPair
   generality: G
   mirror-B: D5/B/S3/Analytic/Knapsack/GreedyFillPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-item greedy coordinates and the return-to-weight ratio exchange inequality. -/

import D5.S3.Analytic.Knapsack.FractionalKnapsackDual

open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Knapsack.GreedyFillPair

open FractionalKnapsackDual

variable {ι : Type*} [DecidableEq ι]

/-- The complete allocation on a two-item list, with no sign restrictions. -/
theorem greedyFill_pair (w : ι → ℝ) (a b : ι) (hab : a ≠ b) (B : ℝ) :
    greedyFill w [a, b] B = fun i =>
      if i = a then (if w a ≤ B then 1 else B / w a)
      else if i = b then
        (if w a ≤ B then (if w b ≤ B - w a then 1 else (B - w a) / w b) else 0)
      else 0 := by
  funext i
  by_cases ha : w a ≤ B <;> by_cases hb : w b ≤ B - w a <;>
    by_cases hia : i = a <;> by_cases hib : i = b <;>
    simp [greedyFill, ha, hb, Function.update_apply, hia, hib]

/-- The first coordinate depends only on the first weight and the budget. -/
theorem greedyFill_pair_apply_left (w : ι → ℝ) (a b : ι) (hab : a ≠ b) (B : ℝ) :
    greedyFill w [a, b] B a = if w a ≤ B then 1 else B / w a := by
  rw [greedyFill_pair w a b hab B]
  simp

/-- The second coordinate receives only the budget left after filling the first. -/
theorem greedyFill_pair_apply_right (w : ι → ℝ) (a b : ι) (hab : a ≠ b) (B : ℝ) :
    greedyFill w [a, b] B b =
      if w a ≤ B then (if w b ≤ B - w a then 1 else (B - w a) / w b) else 0 := by
  rw [greedyFill_pair w a b hab B]
  simp [hab.symm]

/-- Only the two listed coordinates contribute to the return. -/
theorem objective_greedyFill_pair [Fintype ι] (w v : ι → ℝ)
    (a b : ι) (hab : a ≠ b) (B : ℝ) :
    objective v (greedyFill w [a, b] B) =
      if w a ≤ B then v a + (if w b ≤ B - w a then v b else
        (v b / w b) * (B - w a)) else (v a / w a) * B := by
  have hsum : objective v (greedyFill w [a, b] B) =
      v a * greedyFill w [a, b] B a + v b * greedyFill w [a, b] B b := by
    apply Finset.sum_eq_add_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab
    intro i _ hi
    rw [greedyFill_pair w a b hab B]
    simp [hi.1, hi.2]
  rw [hsum, greedyFill_pair_apply_left w a b hab B,
    greedyFill_pair_apply_right w a b hab B]
  split_ifs <;> ring

/-- Putting the larger return-to-weight ratio first cannot decrease the two-item return. -/
theorem greedyFill_pair_swap [Fintype ι] (w v : ι → ℝ)
    (a b : ι) (hab : a ≠ b) (B : ℝ) (hwa : 0 < w a) (hwb : 0 < w b)
    (hB : 0 ≤ B) (hratio : v b / w b ≤ v a / w a) :
    objective v (greedyFill w [b, a] B) ≤ objective v (greedyFill w [a, b] B) := by
  rw [objective_greedyFill_pair w v b a hab.symm B,
    objective_greedyFill_pair w v a b hab B]
  have hva : v a = (v a / w a) * w a := (div_mul_cancel₀ _ hwa.ne').symm
  have hvb : v b = (v b / w b) * w b := (div_mul_cancel₀ _ hwb.ne').symm
  by_cases htotal : w a + w b ≤ B
  · have ha : w a ≤ B := by linarith
    have hb : w b ≤ B := by linarith
    have har : w a ≤ B - w b := by linarith
    have hbr : w b ≤ B - w a := by linarith
    simp only [if_pos ha, if_pos hb, if_pos har, if_pos hbr]
    linarith
  · have har : ¬w a ≤ B - w b := by linarith
    have hbr : ¬w b ≤ B - w a := by linarith
    simp only [if_neg har, if_neg hbr]
    by_cases ha : w a ≤ B <;> by_cases hb : w b ≤ B
    · simp only [if_pos ha, if_pos hb]
      have hgain := mul_nonneg (sub_nonneg.mpr hratio)
        (show 0 ≤ w a + w b - B by linarith)
      nlinarith [hva, hvb]
    · simp only [if_pos ha, if_neg hb]
      have hgain := mul_nonneg (sub_nonneg.mpr hratio) hwa.le
      nlinarith [hva]
    · simp only [if_neg ha, if_pos hb]
      have hgain := mul_nonneg (sub_nonneg.mpr hratio) hwb.le
      nlinarith [hvb]
    · simp only [if_neg ha, if_neg hb]
      exact mul_le_mul_of_nonneg_right hratio hB

#print axioms greedyFill_pair
#print axioms greedyFill_pair_apply_left
#print axioms greedyFill_pair_apply_right
#print axioms objective_greedyFill_pair
#print axioms greedyFill_pair_swap

end D5.S3.Analytic.Knapsack.GreedyFillPair
