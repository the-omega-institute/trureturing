/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/BinCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/BinCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative cutoff bounds for signed frequency bins and weighted degree samples. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.BinSquareTail

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open MeasureTheory Real Set
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

open Finset

theorem signed_bin_tail_inv_three_halves (H : ℕ) (hH : 0 < H) :
    (∑' k : ℤ, if k.natAbs ≤ H then 0 else (|(k : ℝ)| + 1) ^ (-3 / 2 : ℝ)) ≤
      4 * (H : ℝ) ^ (-1 / 2 : ℝ) := by
  convert signed_bin_tail_rpow H hH (s := -3/2) (by norm_num) using 1
  norm_num
  ring

/-- The signed bins up to height `H` have power-bounded total mass. -/
theorem signed_bin_head_inv_three_quarters (H : ℕ) :
    (∑ k ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), (|(k : ℝ)| + 1) ^ (-3 / 4 : ℝ)) ≤
      8 * ((H + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
  let bins := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let positive (k : ℤ) : Prop := 0 ≤ k
  let weight (k : ℤ) : ℝ := (|(k : ℝ)| + 1) ^ (-3 / 4 : ℝ)
  let toIndex (k : ℤ) : ℕ := k.natAbs + 1
  let indices := Finset.Ioc 0 (H + 1)
  let term (n : ℕ) : ℝ := (n : ℝ) ^ (-3 / 4 : ℝ)
  have hindex : bins.image toIndex ⊆ indices := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hk
    apply Finset.mem_Ioc.mpr
    dsimp [toIndex]
    omega
  have hterm (k : ℤ) : weight k = term (toIndex k) := by
    dsimp [weight, term, toIndex]
    rw [Nat.cast_add_one]
    have habs : (k.natAbs : ℝ) = |(k : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs]
  have hcompare {s : Finset ℤ} (hsub : s ⊆ bins) (hinj : Set.InjOn toIndex (s : Set ℤ)) :
      ∑ k ∈ s, weight k ≤ ∑ n ∈ indices, term n := by
    apply Finset.sum_le_sum_of_injOn toIndex hinj
    · exact (Finset.image_subset_image hsub).trans hindex
    · intro k _
      exact (hterm k).le
    · intro n _ _
      exact rpow_nonneg (Nat.cast_nonneg n) _
  have hpos : Set.InjOn toIndex (bins.filter positive : Set ℤ) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    exact (Int.natAbs_inj_of_nonneg_of_nonneg ha' hb').mp (Nat.add_right_cancel hab)
  have hneg : Set.InjOn toIndex (bins.filter (fun k => ¬positive k) : Set ℤ) := by
    intro a ha b hb hab
    have ha' : ¬(0 : ℤ) ≤ a := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' : ¬(0 : ℤ) ≤ b := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    exact (Int.natAbs_inj_of_nonpos_of_nonpos (by omega) (by omega)).mp (Nat.add_right_cancel hab)
  change ∑ k ∈ bins, weight k ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not bins positive weight]
  have hp := hcompare (Finset.filter_subset _ _) hpos
  have hn := hcompare (Finset.filter_subset _ _) hneg
  have hsum : ∑ n ∈ indices, term n ≤ 4 * ((H + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) :=
    by simpa only [indices, term, neg_div] using inverse_three_quarters_sum (N := H + 1) (Nat.succ_pos H)
  linarith only [hp, hn, hsum]

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

private theorem double_log_bound {x : ℝ} (hx : 3 ≤ x) (hlog : 1 ≤ Real.log x) :
    1 + Real.log (Real.log (x + 1)) ≤ 8 * (Real.log x) ^ (2 / 5 : ℝ) := by
  have hlog0 : 0 < Real.log x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogplus : Real.log (x + 1) ≤ 2 * Real.log x := by
    have h := Real.log_le_log (by linarith : 0 < x + 1) (show x + 1 ≤ x^2 by nlinarith)
    rwa [pow_two, Real.log_mul hx0.ne' hx0.ne', ← two_mul] at h
  have hll := Real.log_le_log (Real.log_pos (by linarith : 1 < x + 1)) hlogplus
  rw [Real.log_mul (by norm_num) hlog0.ne'] at hll
  have hpow := Real.one_le_rpow hlog (by norm_num : (0 : ℝ) ≤ 2/5)
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogt := Real.log_le_rpow_div hlog0.le (by norm_num : (0 : ℝ) < 2/5)
  linarith only [hll, hpow, hlog2, hlogt]

/-- The logarithmic degree cutoff and the two arithmetic losses have a common scale. -/
theorem logarithmic_order_cutoff_bounds :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x ≥ X,
      let t := Real.log x
      let ell := 1 + Real.log (Real.log (x + 1))
      let L := ell / 8
      2 ≤ t ∧ 1 ≤ L ∧ L ≤ x ∧
        Real.sqrt ell * t ^ (-1 / 5 : ℝ) ≤ 3 ∧
        Real.sqrt ell * (Real.exp (2 * L) / t) ≤ 12 := by
  let X := Real.exp (Real.exp 8)
  have hX3 : 3 ≤ X := by
    have h8 := Real.add_one_le_exp (8 : ℝ)
    have h2 := Real.add_one_le_exp (Real.exp 8)
    dsimp [X]
    linarith
  refine ⟨X, hX3, fun x hx => ?_⟩
  dsimp only
  let t := Real.log x
  let ell := 1 + Real.log (Real.log (x + 1))
  let L := ell / 8
  change 2 ≤ t ∧ 1 ≤ L ∧ L ≤ x ∧ Real.sqrt ell * t^(-1 / 5 : ℝ) ≤ 3 ∧
    Real.sqrt ell * (Real.exp (2 * L) / t) ≤ 12
  have hx3 := hX3.trans hx
  have hx0 : 0 < x := by linarith
  have ht8 : Real.exp 8 ≤ t := by
    simpa [X, t] using Real.log_le_log (Real.exp_pos (Real.exp 8)) hx
  have ht₂ : 2 ≤ t := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have ht : 1 ≤ t := by linarith
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hplus : t ≤ Real.log (x+1) := Real.log_le_log hx0 (by linarith)
  have hll : 8 ≤ Real.log (Real.log (x+1)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 8) (ht8.trans hplus)
  have hL : 1 ≤ L := by dsimp [L, ell]; linarith
  have hell0 : 0 ≤ ell := by dsimp [ell]; linarith
  have hLx : L ≤ x := by
    have hle : Real.log (Real.log (x + 1)) ≤ x := by
      have hlogplus0 : 0 < Real.log (x + 1) := ht0.trans_le hplus
      linarith [Real.log_le_sub_one_of_pos hlogplus0, Real.log_le_sub_one_of_pos (by linarith : 0 < x+1)]
    dsimp [L, ell]
    linarith
  have hsqrt : Real.sqrt ell ≤ 3 * t ^ (1 / 5 : ℝ) := by
    have hsb := double_log_bound hx3 ht
    have hpsq : (t ^ (1/5 : ℝ))^2 = t^(2/5 : ℝ) := by
      rw [← Real.rpow_mul_natCast ht0.le]
      congr 1
      norm_num
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, hpsq]
      have hp := Real.rpow_nonneg ht0.le (2/5)
      norm_num
      linarith only [hsb, hp]
  have hinv : t^(-1/5 : ℝ) = (t^(1/5 : ℝ))⁻¹ := by
    rw [show (-1/5 : ℝ) = -(1/5) by ring, Real.rpow_neg ht0.le]
  have htroot : 0 < t^(1/5 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hfirst : Real.sqrt ell * t^(-1/5 : ℝ) ≤ 3 := by
    rw [hinv, ← div_eq_mul_inv]
    exact (div_le_iff₀ htroot).mpr hsqrt
  have hlogplus : Real.log (x + 1) ≤ 2*t := by
    have h := Real.log_le_log (by linarith : 0 < x+1) (show x+1 ≤ x^2 by nlinarith)
    rwa [pow_two, Real.log_mul hx0.ne' hx0.ne', ← two_mul] at h
  have hexact : Real.exp (2 * L) =
      Real.exp (1 / 4) * (Real.log (x + 1)) ^ (1 / 4 : ℝ) := by
    rw [show 2 * L = 1 / 4 + Real.log (Real.log (x + 1)) * (1 / 4) by dsimp [L, ell]; ring,
      Real.exp_add, Real.rpow_def_of_pos (ht0.trans_le hplus)]
  have hexp4 : Real.exp (1/4) ≤ 2 := by
    have hlog2 : (1 / 4 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      linarith
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hlog2
  have hb : (Real.log (x + 1)) ^ (1 / 4 : ℝ) ≤ 2 * t ^ (1 / 4 : ℝ) := by
    refine (Real.rpow_le_rpow (ht0.trans_le hplus).le hlogplus (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) ht0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht0.le _)
    simpa using (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 / 4 : ℝ) ≤ 1))
  have hExp : Real.exp (2 * L) ≤ 4 * t ^ (1 / 4 : ℝ) := by
    rw [hexact]
    exact (mul_le_mul hexp4 hb (Real.rpow_nonneg (ht0.trans_le hplus).le _) (by norm_num)).trans_eq (by ring)
  have hProd : t^(1/5 : ℝ) * t^(1/4 : ℝ) ≤ t := by
    rw [← Real.rpow_add ht0]
    simpa using (Real.rpow_le_rpow_of_exponent_le ht
      (by norm_num : (1/5 : ℝ) + 1/4 ≤ 1))
  refine ⟨ht₂, hL, hLx, hfirst, ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ ht0).mpr
  calc
    _ ≤ (3 * t ^ (1/5 : ℝ)) * (4 * t ^ (1/4 : ℝ)) :=
      mul_le_mul hsqrt hExp (Real.exp_nonneg _) (by positivity)
    _ = 12 * (t ^ (1/5 : ℝ) * t ^ (1/4 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hProd (by norm_num)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
