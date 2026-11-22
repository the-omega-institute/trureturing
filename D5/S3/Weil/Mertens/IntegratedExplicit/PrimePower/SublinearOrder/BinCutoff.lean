/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/BinCutoff
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/BinCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative cutoff bounds for signed frequency bins and weighted degree samples. -/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open MeasureTheory Real Set

private theorem one_sided_tail (H : ℕ) (hH : 0 < H) :
    (∑' n : ℕ, ((n + H + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ≤
      2 * (H : ℝ) ^ (-1 / 2 : ℝ) := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have anti : AntitoneOn (fun x : ℝ => x ^ (-3 / 2 : ℝ)) (Ici (H : ℝ)) := by
    intro x hx y _ hxy
    exact rpow_le_rpow_of_nonpos (hH'.trans_le hx) hxy (by norm_num)
  have h := AntitoneOn.tsum_comp_add_le_integral H anti
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hH')
    (fun x hx => rpow_nonneg (hH'.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hH'] at h
  convert h using 1
  norm_num
  ring

open Finset

/-- The square tail outside the symmetric interval of frequency bins. -/
theorem signed_bin_tail_inv_three_halves (H : ℕ) (hH : 0 < H) :
    (∑' k : ℤ, if k.natAbs ≤ H then 0 else (|(k : ℝ)| + 1) ^ (-3 / 2 : ℝ)) ≤
      4 * (H : ℝ) ^ (-1 / 2 : ℝ) := by
  let f (k : ℤ) : ℝ := if k.natAbs ≤ H then 0 else (|(k : ℝ)| + 1) ^ (-3 / 2 : ℝ)
  let e := Equiv.intEquivNatSumNat.symm
  let g (n : ℕ) : ℝ := if n ≤ H then 0 else ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)
  have hn : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hg : Summable g := Summable.of_nonneg_of_le (fun n => by
    dsimp [g]
    split <;> positivity) (fun n => by
    dsimp [g]
    split
    · positivity
    · exact le_rfl) ((summable_nat_add_iff 1).2 hn)
  have gh0 : g 0 = 0 := by simp [g]
  have epos (n : ℕ) : f (e (Sum.inl n)) = g n := by
    change f (n : ℤ) = _
    simp [f, g, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  have eneg (n : ℕ) : f (e (Sum.inr n)) = g (n + 1) := by
    change f (Int.negSucc n) = _
    have habs : |(Int.negSucc n : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
      rw [Int.cast_negSucc, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [f, g]
    rw [Int.natAbs_negSucc, Nat.succ_eq_add_one, habs, Nat.cast_add_one (n + 1)]
  have hs₁ : Summable ((f ∘ e) ∘ Sum.inl) := hg.congr (fun n => (epos n).symm)
  have hs₂ : Summable ((f ∘ e) ∘ Sum.inr) :=
    ((summable_nat_add_iff 1).2 hg).congr (fun n => (eneg n).symm)
  have hsplit := hg.sum_add_tsum_nat_add 1
  simp only [sum_range_one, gh0, zero_add] at hsplit
  have hmain := hg.sum_add_tsum_nat_add (H + 1)
  have hz : ∑ i ∈ range (H + 1), g i = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [g, Nat.lt_succ_iff.mp (mem_range.mp hi)]
  rw [hz, zero_add] at hmain
  have htail : (∑' i : ℕ, g (i + (H + 1))) ≤
      ∑' i : ℕ, ((i + H + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := by
    apply Summable.tsum_le_tsum _ ((summable_nat_add_iff (H + 1)).2 hg)
    · simpa only [Nat.add_assoc] using (summable_nat_add_iff (H + 1)).2 hn
    · intro i
      have hi : ¬i + (H + 1) ≤ H := by omega
      simp only [g, hi, ite_false]
      apply rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast (show i + H + 1 ≤ i + (H + 1) + 1 by omega)
      · norm_num
  change ∑' k, f k ≤ _
  rw [← e.tsum_eq f]
  change ∑' k, (f ∘ e) k ≤ _
  rw [hs₁.tsum_sum hs₂]
  simp only [Function.comp_apply, tsum_congr epos, tsum_congr eneg, hsplit]
  rw [← hmain]
  linarith only [htail, one_sided_tail H hH]

theorem scaled_bin_cutoff_bound {L q u : ℝ} (hL : 1 ≤ L) (hLq : L ≤ q) (hu : L * q ≤ u) :
    ∃ H : ℕ, 0 < H ∧
      (((H : ℝ) + 1) ^ (1 / 4 : ℝ)) * (1 + q^2 / u) +
        q * (H : ℝ) ^ (-1 / 4 : ℝ) ≤ 5 * q / Real.sqrt L := by
  let H := ⌈L^2⌉₊
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hq0 : 0 < q := hL0.trans_le hLq
  have hu0 : 0 < u := (mul_pos hL0 hq0).trans_le hu
  have hHlow : L^2 ≤ (H : ℝ) := Nat.le_ceil _
  have hH : 0 < H := by
    exact_mod_cast (sq_pos_of_pos hL0).trans_le hHlow
  have hHhigh : (H : ℝ) < L^2 + 1 := Nat.ceil_lt_add_one (sq_nonneg L)
  have hS0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hSsq : (Real.sqrt L)^2 = L := Real.sq_sqrt hL0.le
  have hS4 : (2 * Real.sqrt L)^4 = 16 * L^2 := by
    calc
      _ = 16 * ((Real.sqrt L)^2)^2 := by ring
      _ = _ := by rw [hSsq]
  have hHead : ((H : ℝ) + 1) ^ (1 / 4 : ℝ) ≤ 2 * Real.sqrt L := by
    calc
      _ ≤ ((2 * Real.sqrt L) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        rw [hS4]
        nlinarith only [hHhigh, one_le_pow₀ hL (n := 2)]
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * Real.sqrt L)]
        norm_num
  have hTail : (H : ℝ) ^ (-1 / 4 : ℝ) ≤ (Real.sqrt L)⁻¹ := by
    calc
      _ ≤ (L^2) ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hL0) hHlow (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, Real.sqrt_eq_rpow,
          show ((2 : ℕ) : ℝ) * (-1 / 4) = -(1 / 2) by norm_num, Real.rpow_neg hL0.le]
  have hFrac : q^2 / u ≤ q / L := by
    rw [div_le_div_iff₀ hu0 hL0]
    nlinarith only [mul_le_mul_of_nonneg_left hu hq0.le]
  have hGeom : 1 + q^2 / u ≤ 2 * (q / L) := by
    linarith only [hFrac, (one_le_div hL0).mpr hLq]
  refine ⟨H, hH, ?_⟩
  calc
    _ ≤ (2 * Real.sqrt L) * (2 * (q / L)) + q * (Real.sqrt L)⁻¹ := by
      exact add_le_add (mul_le_mul hHead hGeom (by positivity) (by positivity))
        (mul_le_mul_of_nonneg_left hTail hq0.le)
    _ = _ := by
      field_simp [hL0.ne', hS0.ne']
      rw [hSsq]
      ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
