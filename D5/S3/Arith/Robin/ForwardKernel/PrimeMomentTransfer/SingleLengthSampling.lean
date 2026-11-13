/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cumulative cell sampling preserves scalar moments with explicit endpoint corrections. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMSDefs
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CellQuadrature

/-! Floor sampling of scalar increments on a cumulative interval. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open VarianceTransferDefs
noncomputable section
set_option autoImplicit false

/-- Continuous and lattice increments differ by a logarithmic endpoint error
throughout the prefix. -/
theorem sampling_cumulative_pointwise (Y v x : ℝ) (hY : 2 ≤ Y) (hv : 1 ≤ v)
    (hvY : v ≤ Y) (hx : x ∈ Icc (1 : ℝ) Y) :
    |primeIncrement v x - primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ)| ≤ 2 * Real.log (4 * Y) + 2 := by
  have hv0 : 0 ≤ v := by linarith
  have hx0 : 0 ≤ x := by linarith [hx.1]
  by_cases hlocal : 2 ≤ x ∧ v ≤ x
  · have hp := sampling_pointwise (N := x) (H := v) (M := 1) (a := 0) (b := 1)
      hlocal.1 hv (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [one_mul] using hlocal.2) ⟨le_rfl, by linarith [hx.1]⟩
    have hd : primeIncrement v x = Delta v 0 1 x := by
      simp only [primeIncrement, increment, chebyshevError, Delta, one_mul, zero_mul, add_zero, sub_zero]
      ring
    rw [real_length_cell v ⌊x⌋₊ hv0, ← hd] at hp
    have hlog : Real.log (4 * x) ≤ Real.log (4 * Y) :=
      Real.log_le_log (by linarith [hx.1])
        (mul_le_mul_of_nonneg_left hx.2 (by norm_num))
    linarith only [hp, hlog]
  · let n := ⌊x⌋₊
    let K := ⌊v⌋₊
    have hn : 1 ≤ n := Nat.le_floor (by simpa using hx.1)
    have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
    have ht0 : 0 ≤ x - (n : ℝ) := sub_nonneg.mpr hnx
    have ht1 : x - (n : ℝ) < 1 := by
      linarith [Nat.lt_floor_add_one x]
    have hq : ⌊x + v⌋₊ = n + K ∨ ⌊x + v⌋₊ = n + K + 1 := by
      rw [show x + v = (n : ℝ) + (x - (n : ℝ)) + v by ring]
      exact floor_shift_cases_add_nat ht0 ht1 hv0
    have hpY : (n : ℝ) ≤ 4 * Y := hnx.trans (by linarith [hx.2])
    have hqY : (⌊x + v⌋₊ : ℝ) ≤ 4 * Y :=
      (Nat.floor_le (add_nonneg hx0 hv0)).trans (by linarith [hx.2])
    have hpsi := psi_endpoint_discrepancy (m := n) (m' := n + K)
      (p := n) (q := ⌊x + v⌋₊) (L := Y)
      (Nat.le_add_right _ _) (Or.inl rfl) hq hpY hqY hn (by omega) (by linarith)
    have hlen : |(K : ℝ) - v| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [Nat.floor_le hv0, Nat.lt_floor_add_one v]
    have heq : primeIncrement v x - primeIncrement (K : ℝ) (n : ℝ) =
        ((Chebyshev.psi (⌊x + v⌋₊ : ℝ) - Chebyshev.psi (n : ℝ)) -
          (Chebyshev.psi ((n + K : ℕ) : ℝ) - Chebyshev.psi (n : ℝ))) +
        ((K : ℝ) - v) := by
      dsimp only [primeIncrement, increment, chebyshevError]
      rw [Chebyshev.psi_eq_psi_coe_floor (x + v), Chebyshev.psi_eq_psi_coe_floor x]
      simp only [Nat.cast_add]
      dsimp only [n]
      ring
    change |primeIncrement v x - primeIncrement (K : ℝ) (n : ℝ)| ≤ _
    rw [heq]
    exact ((abs_add_le _ _).trans (add_le_add hpsi hlen)).trans (by linarith)

/-- A lattice increment sampled by the floor function has a finite fourth moment
on a finite interval. -/
theorem step_memLp (Y v : ℝ) :
    MemLp (fun x => primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ)) 4
      (volume.restrict (Icc (1 : ℝ) Y)) := by
  let F : ℕ → ℝ := fun n => primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ)
  have hm := ((measurable_of_countable F).comp Nat.measurable_floor).aestronglyMeasurable
    (μ := volume.restrict (Icc (1 : ℝ) Y))
  apply (integrable_norm_rpow_iff hm (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
  have hi := floor_step_intervalIntegrable
    (fun n => ‖F n‖ ^ (4 : ℝ≥0∞).toReal) 1 Y (by norm_num)
  exact ((intervalIntegrable_iff' (by finiteness)).mp hi).mono_set Icc_subset_uIcc

/-- The terminal cell contributes its fractional length minus one to the prefix sum. -/
theorem floor_integral_identity (F : ℕ → ℝ) (Y : ℝ) (hY : 1 ≤ Y) :
    (∫ x in (1 : ℝ)..Y, F ⌊x⌋₊) - (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, F n) =
      (Y - (⌊Y⌋₊ : ℝ) - 1) * F ⌊Y⌋₊ := by
  have hN : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY)
  have hi := floor_step_integral F 1 Y (by simpa using hY)
  have hs := Finset.sum_Ico_add_eq_sum_Icc (f := F) hN
  have hsets : Finset.Icc 1 ⌊Y⌋₊ = Finset.Ioc 0 ⌊Y⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hsets] at hs
  norm_num only [Nat.cast_one] at hi
  linear_combination hi + hs

/-- The fourth integral of the sampled increment is bounded by its discrete prefix sum. -/
theorem step_fourth_le_sum (Y v : ℝ) (hY : 1 ≤ Y) :
    (∫ x in (1 : ℝ)..Y, |primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ)| ^ 4) ≤
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ := by
  have hi := floor_integral_identity (fun n => |primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ)| ^ 4) Y hY
  have hc : Y - (⌊Y⌋₊ : ℝ) - 1 ≤ 0 := by
    linarith [Nat.lt_floor_add_one Y]
  have he := mul_nonpos_of_nonpos_of_nonneg hc
    (pow_nonneg (abs_nonneg (primeIncrement (⌊v⌋₊ : ℝ) (⌊Y⌋₊ : ℝ))) 4)
  rw [← hi] at he
  have hsum : (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, |primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ)| ^ 4) =
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ := by
    simp only [discretePrimeMoment, Even.pow_abs (show Even 4 by decide)]
  rw [hsum] at he
  exact sub_nonpos.mp he

/-- Fourth moments control the change in a second or fourth scalar moment. -/
theorem scalar_stability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (k : ℕ) (f g : Ω → ℝ) (C e : ℝ)
    (hk : k = 2 ∨ k = 4) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    (hfb : (∫ x, |f x| ^ 4 ∂μ) ≤ C) (hgb : (∫ x, |g x| ^ 4 ∂μ) ≤ C)
    (hdb : (∫ x, |f x - g x| ^ 4 ∂μ) ≤ e ^ 4) :
    |(∫ x, f x ^ k ∂μ) - (∫ x, g x ^ k ∂μ)| ≤
      (k : ℝ) * e * C ^ (((k : ℝ) - 1) / 4) := by
  have hk0 : 0 < k := by rcases hk with rfl | rfl <;> norm_num
  have hk4 : k ≤ 4 := by rcases hk with rfl | rfl <;> norm_num
  have hif := FourthTransfer.FiniteProductMomentBounds.product_integrable hk0
    (f := fun _ : Fin k => f) (fun _ => hf.mono_exponent (by exact_mod_cast hk4))
  have hig := FourthTransfer.FiniteProductMomentBounds.product_integrable hk0
    (f := fun _ : Fin k => g) (fun _ => hg.mono_exponent (by exact_mod_cast hk4))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hif hig
  have hp := FourthTransfer.FiniteProductMomentBounds.product_fourth_difference_bound
    (μ := μ) hk0 hk4 (f := fun _ : Fin k => f) (g := fun _ : Fin k => g)
    hC (show 0 ≤ e ^ 4 by positivity) (fun _ => ⟨hf, hg⟩)
    (fun _ => hfb) (fun _ => hgb) (fun _ => hdb)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  have hroot : (e ^ 4) ^ (1 / 4 : ℝ) = e := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast he (by norm_num : (4 : ℕ) ≠ 0)
  rw [hroot] at hp
  rw [← integral_sub hif hig]
  exact abs_integral_le_integral_abs.trans hp

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
