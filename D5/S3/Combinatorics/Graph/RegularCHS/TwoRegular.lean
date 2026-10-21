/- GID: D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/TwoRegular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Basic.Real.Basic, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.RingTheory.PowerSeries.Substitution, mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: Coefficientwise cycle denominator comparison for positive length partitions. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section
open Classical PowerSeries Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

/-- The cycle denominator factor after the Catalan change of variable. -/
def cycleKernel (l : ℕ) : PowerSeries ℝ :=
  (mk fun k : ℕ => (k + 1 : ℝ)).subst ((X : PowerSeries ℝ) ^ l)

private theorem coeff_cycleKernel {l : ℕ} (hl : 0 < l) (k : ℕ) :
    coeff k (cycleKernel l) = if l ∣ k then ((k / l : ℕ) : ℝ) + 1 else 0 := by
  simp [cycleKernel, coeff_subst_X_pow (Nat.ne_of_gt hl)]

private theorem cycleKernel_nonneg {l : ℕ} (hl : 0 < l) (k : ℕ) :
    0 ≤ coeff k (cycleKernel l) := by
  rw [coeff_cycleKernel hl]
  split_ifs <;> positivity

private theorem coeff_mul_ge_single (A B : PowerSeries ℝ)
    (hA : ∀ k, 0 ≤ coeff k A) (hB : ∀ k, 0 ≤ coeff k B) (i j : ℕ) :
    coeff i A * coeff j B ≤ coeff (i + j) (A * B) := by
  rw [coeff_mul]
  exact Finset.single_le_sum (f := fun p : ℕ × ℕ => coeff p.1 A * coeff p.2 B)
    (fun p _ => mul_nonneg (hA p.1) (hB p.2))
    (by simp : (i, j) ∈ Finset.antidiagonal (i + j))

/-- Merging two positive cycle lengths decreases every denominator coefficient. -/
private theorem cycleKernel_add_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    coeff k (cycleKernel (a + b)) ≤ coeff k (cycleKernel a * cycleKernel b) := by
  by_cases hd : a + b ∣ k
  · obtain ⟨j, rfl⟩ := hd
    have he : (a + b) * j = a * j + b * j := Nat.add_mul a b j
    rw [he]
    have h := coeff_mul_ge_single (cycleKernel a) (cycleKernel b)
      (cycleKernel_nonneg ha) (cycleKernel_nonneg hb) (a * j) (b * j)
    have hleft : coeff (a * j + b * j) (cycleKernel (a + b)) = (j + 1 : ℝ) := by
      rw [← he, coeff_cycleKernel (by omega), if_pos (dvd_mul_right _ _),
        Nat.mul_div_cancel_left j (by omega : 0 < a + b)]
    rw [hleft]
    rw [coeff_cycleKernel ha, coeff_cycleKernel hb,
      if_pos (dvd_mul_right a j), if_pos (dvd_mul_right b j),
      Nat.mul_div_cancel_left j ha, Nat.mul_div_cancel_left j hb] at h
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  · rw [coeff_cycleKernel (by omega), if_neg hd, coeff_mul]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (cycleKernel_nonneg ha p.1) (cycleKernel_nonneg hb p.2)

private theorem coeff_mul_mono_left (A B C : PowerSeries ℝ)
    (hA : ∀ k, 0 ≤ coeff k A) (hBC : ∀ k, coeff k B ≤ coeff k C) (k : ℕ) :
    coeff k (A * B) ≤ coeff k (A * C) := by
  simp only [coeff_mul]
  exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hBC p.2) (hA p.1)

/-- A single cycle denominator is dominated by the product for a partition of its length. -/
theorem cycleKernel_sum_le_prod (ls : List ℕ) (hne : ls ≠ [])
    (hpos : ∀ l ∈ ls, 0 < l) (k : ℕ) :
    coeff k (cycleKernel ls.sum) ≤ coeff k (ls.map cycleKernel).prod := by
  induction ls generalizing k with
  | nil => exact (hne rfl).elim
  | cons a ls ih =>
    cases ls with
    | nil => simp
    | cons b tail =>
      have ha := hpos a (by simp)
      have hrest : ∀ l ∈ b :: tail, 0 < l := by
        intro l hl
        exact hpos l (List.mem_cons_of_mem a hl)
      have hb : 0 < (b :: tail).sum := by
        have := hrest b (by simp)
        simp only [List.sum_cons]
        omega
      calc
        coeff k (cycleKernel (a :: b :: tail).sum) ≤
            coeff k (cycleKernel a * cycleKernel (b :: tail).sum) :=
          cycleKernel_add_le ha hb k
        _ ≤ coeff k (cycleKernel a * ((b :: tail).map cycleKernel).prod) :=
          coeff_mul_mono_left _ _ _ (cycleKernel_nonneg ha)
            (fun j => ih (by simp) hrest j) k
        _ = _ := by simp

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
