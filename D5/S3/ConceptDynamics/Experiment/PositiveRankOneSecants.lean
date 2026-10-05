/- GID: D5/S3/ConceptDynamics/Experiment/PositiveRankOneSecants
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/PositiveRankOneSecants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nonzero traceless real matrix is a positive rank-one secant exactly when its diagonal is nonzero or its offdiagonal product is negative. -/

import D5.S3.ConceptDynamics.Experiment.SelfCalibratingRulings
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace D5.S3.ConceptDynamics.Experiment.PositiveRankOneSecants

open SelfCalibratingRulings (Source)

/-- The exact criterion for a nonzero traceless matrix to be the difference of
two strictly positive rank-one sources. -/
theorem result (a b c : ℝ)
    (hnonzero : (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) :
    (∃ R₀ R₁ : Source, (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) ℝ) =
      R₁.val - R₀.val) ↔ a ≠ 0 ∨ b * c < 0 := by
  constructor
  · rintro ⟨R₀, R₁, hdifference⟩
    by_cases ha : a = 0
    · right
      have e₀₀ := congrArg (fun R : Matrix (Fin 2) (Fin 2) ℝ => R 0 0) hdifference
      have e₀₁ := congrArg (fun R : Matrix (Fin 2) (Fin 2) ℝ => R 0 1) hdifference
      have e₁₀ := congrArg (fun R : Matrix (Fin 2) (Fin 2) ℝ => R 1 0) hdifference
      have e₁₁ := congrArg (fun R : Matrix (Fin 2) (Fin 2) ℝ => R 1 1) hdifference
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.head_fin_const, Matrix.sub_apply] at e₀₀ e₀₁ e₁₀ e₁₁
      have hp : R₁.val 0 0 = R₀.val 0 0 := by rw [ha] at e₀₀; linarith
      have hs : R₁.val 1 1 = R₀.val 1 1 := by rw [ha] at e₁₁; linarith
      have hproduct : R₁.val 0 1 * R₁.val 1 0 = R₀.val 0 1 * R₀.val 1 0 := by
        rw [← R₁.property.2, hp, hs, R₀.property.2]
      have hbalance : b * R₁.val 1 0 + c * R₀.val 0 1 = 0 := by
        linear_combination hproduct + R₁.val 1 0 * e₀₁ + R₀.val 0 1 * e₁₀
      have hb : b ≠ 0 := by
        intro hb
        have hc : c = 0 := by
          have hz : c * R₀.val 0 1 = 0 := by simpa [hb] using hbalance
          exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (R₀.property.1 0 1))
        apply hnonzero
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
      rcases lt_or_gt_of_ne hb with hb | hb
      · have hc : 0 < c := by
          by_contra hc
          have hcp : c * R₀.val 0 1 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc) (R₀.property.1 0 1).le
          have hbp : b * R₁.val 1 0 < 0 := mul_neg_of_neg_of_pos hb (R₁.property.1 1 0)
          linarith
        exact mul_neg_of_neg_of_pos hb hc
      · have hc : c < 0 := by
          by_contra hc
          have hcp : 0 ≤ c * R₀.val 0 1 :=
            mul_nonneg (le_of_not_gt hc) (R₀.property.1 0 1).le
          have hbp : 0 < b * R₁.val 1 0 := mul_pos hb (R₁.property.1 1 0)
          linarith
        exact mul_neg_of_pos_of_neg hb hc
    · exact Or.inl ha
  · intro hcriterion
    by_cases ha : a ≠ 0
    · let L : ℝ := 1 + |b| + |c|
      let T : ℝ := (a ^ 2 + b * c + (b + c) * L) / a
      let H : ℝ := Real.sqrt (T ^ 2 + 4 * L ^ 2)
      let p : ℝ := (H - T) / 2
      let s : ℝ := (H + T) / 2
      have hL : 0 < L := by dsimp [L]; positivity
      have hLb : 0 < L + b := by dsimp [L]; linarith [neg_abs_le b, abs_nonneg c]
      have hLc : 0 < L + c := by dsimp [L]; linarith [neg_abs_le c, abs_nonneg b]
      have hHsquare : H ^ 2 = T ^ 2 + 4 * L ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hTH : T < H := Real.lt_sqrt_of_sq_lt (by nlinarith [sq_pos_of_pos hL])
      have hnTH : -T < H := Real.lt_sqrt_of_sq_lt (by nlinarith [sq_pos_of_pos hL])
      have hp : 0 < p := by dsimp [p]; linarith
      have hs : 0 < s := by dsimp [s]; linarith
      have hps : p * s = L * L := by dsimp only [p, s]; nlinarith [hHsquare]
      have hsp : s - p = T := by dsimp only [p, s]; ring
      have haT : a * T = a ^ 2 + b * c + (b + c) * L := by
        dsimp only [T]
        field_simp [ha]
      have hrank : (p + a) * (s - a) = (L + b) * (L + c) := by
        linear_combination hps + a * hsp - haT
      have hpositive : 0 < p + a ∧ 0 < s - a := by
        have hprod : 0 < (p + a) * (s - a) := by rw [hrank]; exact mul_pos hLb hLc
        rcases lt_or_gt_of_ne ha with ha | ha
        · have hsa : 0 < s - a := by linarith
          exact ⟨(mul_pos_iff_of_pos_right hsa).mp hprod, hsa⟩
        · have hpa : 0 < p + a := by linarith
          exact ⟨hpa, (mul_pos_iff_of_pos_left hpa).mp hprod⟩
      let R₀ : Source := ⟨!![p, L; L, s], by
        constructor
        · intro i j
          fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
          · exact hp
          · exact hL
          · exact hL
          · exact hs
        · simpa using hps⟩
      let R₁ : Source := ⟨!![p + a, L + b; L + c, s - a], by
        constructor
        · intro i j
          fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
          · exact hpositive.1
          · exact hLb
          · exact hLc
          · exact hpositive.2
        · simpa using hrank⟩
      refine ⟨R₀, R₁, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [R₀, R₁] <;> ring
    · have hz : a = 0 := not_ne_iff.mp ha
      have hbc : b * c < 0 := hcriterion.resolve_left ha
      have construct : ∀ (u v : ℝ), 0 < u → v < 0 →
          ∃ R₀ R₁ : Source, (!![0, u; v, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
            R₁.val - R₀.val := by
        intro u v hu hv
        let d := Real.sqrt (-2 * u * v)
        have hrad : 0 < -2 * u * v := by nlinarith [mul_neg_of_pos_of_neg hu hv]
        have hd : 0 < d := Real.sqrt_pos.mpr hrad
        have hdsquare : d ^ 2 = -2 * u * v := Real.sq_sqrt hrad.le
        let R₀ : Source := ⟨!![d, u; -2 * v, d], by
          constructor
          · intro i j
            fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
            · exact hd
            · exact hu
            · linarith
            · exact hd
          · change d * d = u * (-2 * v)
            nlinarith [hdsquare]⟩
        let R₁ : Source := ⟨!![d, 2 * u; -v, d], by
          constructor
          · intro i j
            fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
            · exact hd
            · linarith
            · linarith
            · exact hd
          · change d * d = (2 * u) * (-v)
            nlinarith [hdsquare]⟩
        refine ⟨R₀, R₁, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [R₀, R₁] <;> ring
      rcases mul_neg_iff.mp hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · simpa [hz] using construct b c hb hc
      · obtain ⟨R₀, R₁, hdifference⟩ := construct (-b) (-c) (by linarith) (by linarith)
        refine ⟨R₁, R₀, ?_⟩
        have he := congrArg Neg.neg hdifference
        simpa [hz, neg_sub] using he

end D5.S3.ConceptDynamics.Experiment.PositiveRankOneSecants
