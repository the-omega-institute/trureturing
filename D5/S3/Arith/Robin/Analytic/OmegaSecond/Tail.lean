/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Tail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponentially small integer bounds outside the central moving-weight interval. -/

import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail

private lemma log_softplus_le_exp (v : ℝ) : log (1 + exp v) ≤ exp v := by
  simpa only [add_sub_cancel_left] using log_le_sub_one_of_pos (by positivity : 0 < 1 + exp v)

/-- An inverse-power sum over any finite set beyond an integer cutoff. -/
theorem finite_power_tail {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N)
    (S : Finset ℕ) (hS : ∀ n ∈ S, N < n) :
    ∑ n ∈ S, (n : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  classical
  let M := S.sup id
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : S ⊆ Finset.Ioc N M := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hS n hn, Finset.le_sup (f := id) hn⟩
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s)) (Icc (N : ℝ) M) := by
    intro a ha b hb hab
    exact rpow_le_rpow_of_nonpos (hN0.trans_le ha.1) hab (by linarith)
  have hsum : (∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s)) =
      ∑ n ∈ Finset.Ico N M, ((n + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, ← Finset.sum_Ico_add']
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := hsum
    _ ≤ ∫ t in Ioi (N : ℝ), t ^ (-s) :=
      hanti.sum_Ico_le_integral (integrableOn_Ioi_rpow_of_lt (by linarith) hN0)
        (fun t ht => rpow_nonneg (hN0.trans ht).le _)
    _ = (N : ℝ) ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hN0]
      rw [show -s + 1 = 1 - s by ring]
      have h1 : s - 1 ≠ 0 := by linarith
      have h2 : 1 - s ≠ 0 := by linarith
      field_simp [h1, h2]
      ring

/-- The small side is bounded by the number of integers times geometric decay. -/
theorem small_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 0 ≤ s)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ P / 2) :
    ∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ P * (1 / 2 : ℝ) ^ s := by
  have hP0 : 0 < P := by linarith
  have hsub : S ⊆ Finset.Icc 1 ⌊P / 2⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(hS n hn).1, (Nat.le_floor_iff (by positivity)).mpr (hS n hn).2⟩
  have hcard : (S.card : ℝ) ≤ P := by
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hc
    have hc' : (S.card : ℝ) ≤ ⌊P / 2⌋₊ := by exact_mod_cast hc
    exact hc'.trans ((Nat.floor_le (by positivity)).trans (by linarith))
  have hpoint (n : ℕ) (hn : n ∈ S) :
      log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ (1 / 2 : ℝ) ^ s := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hS n hn).1
    have hratio : (n : ℝ) / P ≤ 1 / 2 := (div_le_iff₀ hP0).mpr (by linarith [(hS n hn).2])
    have hl : log ((n : ℝ) / P) ≤ log (1 / 2 : ℝ) :=
      log_le_log (div_pos hn0 hP0) hratio
    have hl0 : log ((n : ℝ) / P) ≤ 0 :=
      log_nonpos (div_nonneg hn0.le hP0.le) (hratio.trans (by norm_num))
    refine (log_softplus_le_exp _).trans ?_
    rw [abs_of_nonpos hl0, neg_mul_neg,
      rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ ∑ n ∈ S, (1 / 2 : ℝ) ^ s := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (1 / 2 : ℝ) ^ s := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (rpow_nonneg (by norm_num) _)

/-- The large side is bounded using all integers and an actual tail integral. -/
theorem large_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 2 ≤ s)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 2 * P < (n : ℝ)) :
    ∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤
      2 * P * (2 / 3 : ℝ) ^ s := by
  have hP0 : 0 < P := by linarith
  let N := ⌊2 * P⌋₊
  have hNlo : 3 * P / 2 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * P)
    dsimp [N]
    linarith
  have hN0 : (0 : ℝ) < N := by nlinarith
  have hNN : 0 < N := by exact_mod_cast hN0
  have hS' : ∀ n ∈ S, N < n := by
    intro n hn
    exact (Nat.floor_lt (by positivity : 0 ≤ 2 * P)).mpr (hS n hn)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ P ^ s * (n : ℝ) ^ (-s) := by
    have hn0 : (0 : ℝ) < n := by linarith [hS n hn]
    have hratio : 1 ≤ (n : ℝ) / P := (le_div_iff₀ hP0).mpr (by linarith [hS n hn])
    have hl : 0 ≤ log ((n : ℝ) / P) := log_nonneg hratio
    refine (log_softplus_le_exp _).trans_eq ?_
    rw [abs_of_nonneg hl, log_div hn0.ne' hP0.ne',
      rpow_def_of_pos hP0, rpow_def_of_pos hn0, ← exp_add]
    congr 1
    ring
  have hfinite := finite_power_tail (by linarith : 1 < s) hNN S hS'
  have hmono : (N : ℝ) ^ (1 - s) ≤ (3 * P / 2) ^ (1 - s) :=
    rpow_le_rpow_of_nonpos (by positivity) hNlo (by linarith)
  have hid : P ^ s * (3 * P / 2) ^ (1 - s) =
      (3 * P / 2) * (2 / 3 : ℝ) ^ s := by
    rw [rpow_sub (by positivity), rpow_one]
    calc
      P ^ s * ((3 * P / 2) / (3 * P / 2) ^ s) =
          (3 * P / 2) * (P ^ s / (3 * P / 2) ^ s) := by ring
      _ = (3 * P / 2) * (P / (3 * P / 2)) ^ s := by
        rw [div_rpow hP0.le (by positivity)]
      _ = _ := by
        congr 2
        field_simp [hP0.ne']
        <;> ring
  calc
    _ ≤ ∑ n ∈ S, P ^ s * (n : ℝ) ^ (-s) := Finset.sum_le_sum hpoint
    _ = P ^ s * ∑ n ∈ S, (n : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ P ^ s * ((N : ℝ) ^ (1 - s) / (s - 1)) :=
      mul_le_mul_of_nonneg_left hfinite (rpow_nonneg hP0.le _)
    _ ≤ P ^ s * ((3 * P / 2) ^ (1 - s) / (s - 1)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmono (by linarith)) (rpow_nonneg hP0.le _)
    _ = ((3 * P / 2) * (2 / 3 : ℝ) ^ s) / (s - 1) := by rw [← mul_div_assoc, hid]
    _ ≤ (3 * P / 2) * (2 / 3 : ℝ) ^ s :=
      div_le_self (by positivity) (by linarith)
    _ ≤ _ := by gcongr; linarith

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail
