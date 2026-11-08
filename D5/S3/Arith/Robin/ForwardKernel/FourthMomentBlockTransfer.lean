/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite frozen blocks and logarithmic Riemann sums transfer fixed-scale moments. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthMomentTransferDefs
import D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicScaling

/-! Fixed block convergence and Riemann sums for the logarithmic position law. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentBlockTransfer

open Set MeasureTheory Filter
open scoped Topology BigOperators
open FourthMomentTransferDefs MovingLengthCells DyadicProbability MomentTransferDefs

noncomputable section
set_option autoImplicit false

/-- Fixed-scale interval moments converge after weighting and summing finitely many cells. -/
theorem fixed_block_moments_tendsto
    {E : ℝ → ℝ} {θ : ℝ} {k : ℕ} {W : (Fin k → ℝ) → ℝ}
    (hF : FixedScaleMixedMoments E θ k W)
    (b : Fin k → ℝ → ℝ) (w : ℝ → ℝ) {M : ℝ} {n : ℕ}
    (hM : 0 < M) (hn : 0 < n)
    (hb : ∀ i, ∀ j < n, b i (cellPoint n j) ∈ Icc (0 : ℝ) M) :
    Tendsto (fun X : ℝ => ∑ j ∈ Finset.range n,
      w (cellPoint n j) * fixedBlockMoment E θ k
        (fun i => b i (cellPoint n j)) (cellPoint n j) (cellPoint n (j + 1)) X)
      atTop (𝓝 (∑ j ∈ Finset.range n,
        w (cellPoint n j) * (dyadicProbabilityMeasure 1).real
          (Icc (cellPoint n j) (cellPoint n (j + 1))) *
          W (fun i => b i (cellPoint n j)))) := by
  apply tendsto_finsetSum
  intro j hj
  have hjn := Finset.mem_range.mp hj
  simpa only [mul_assoc] using
    (hF M hM (fun i => b i (cellPoint n j)) (fun i => hb i j hjn)
      _ _ (cellPoint_mem hn hjn.le).1 (cellPoint_lt hn j)
      (cellPoint_mem hn (Nat.succ_le_of_lt hjn)).2).const_mul (w (cellPoint n j))

private lemma block_weight_error {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    |(1 / (n : ℝ)) / (cellPoint n j * Real.log 2) -
      (dyadicProbabilityMeasure 1).real (Icc (cellPoint n j) (cellPoint n (j + 1)))| ≤
        1 / ((n : ℝ) ^ 2 * Real.log 2) := by
  let l := cellPoint n j
  let r := cellPoint n (j + 1)
  have hl : 1 ≤ l := (cellPoint_mem hn hj.le).1
  have hr : r ≤ 2 := (cellPoint_mem hn (Nat.succ_le_of_lt hj)).2
  have hlr : l < r := cellPoint_lt hn j
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : r - l = 1 / (n : ℝ) := cellPoint_step hn j
  have hi : IntervalIntegrable (fun u : ℝ => 1 / (u * Real.log 2)) volume l r := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.mul continuousOn_const)
    intro u hu
    rw [uIcc_of_le hlr.le] at hu
    exact mul_ne_zero (ne_of_gt (show 0 < u by linarith [hu.1])) hlog.ne'
  have hm : (dyadicProbabilityMeasure 1).real (Icc l r) =
      ∫ u in l..r, 1 / (u * Real.log 2) := by
    rw [block_mass hl hlr.le hr]
    simp_rw [div_mul_eq_div_div]
    rw [intervalIntegral.integral_div, integral_one_div_of_pos (by linarith) (by linarith)]
  rw [hm]
  have he : (1 / (n : ℝ)) / (l * Real.log 2) -
      (∫ u in l..r, 1 / (u * Real.log 2)) =
      ∫ u in l..r, (1 / (l * Real.log 2) - 1 / (u * Real.log 2)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const, smul_eq_mul, hstep]
    ring
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := 1 / ((n : ℝ) * Real.log 2))
    (f := fun u => 1 / (l * Real.log 2) - 1 / (u * Real.log 2)) (by
      intro u hu
      rw [uIoc_of_le hlr.le] at hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hl0 : 0 < l := by linarith
      have hnonneg : 0 ≤ 1 / (l * Real.log 2) - 1 / (u * Real.log 2) := by
        exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_right hu.1.le hlog.le))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) * Real.log 2)).mpr
      have hlu : 1 ≤ l * u := by nlinarith [hu.1]
      have hgap : (u - l) * (n : ℝ) ≤ 1 := by
        have := hu.2
        have hs := (eq_div_iff hnR.ne').mp hstep
        nlinarith
      field_simp
      nlinarith)
  rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hlr), hstep] at hb
  convert hb using 1 <;> field_simp <;> ring

/-- Exact logarithmic cell masses give Riemann sums for every continuous function on [1,2]. -/
theorem logarithmic_block_riemann (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (1 : ℝ) 2)) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n,
      f (cellPoint n j) * (dyadicProbabilityMeasure 1).real
        (Icc (cellPoint n j) (cellPoint n (j + 1))))
      atTop (𝓝 (∫ u, f u ∂dyadicProbabilityMeasure 1)) := by
  let g := fun u : ℝ => f u / (u * Real.log 2)
  have hg : ContinuousOn g (Icc (1 : ℝ) 2) := by
    apply hf.div (continuousOn_id.mul continuousOn_const)
    intro u hu
    exact mul_ne_zero (ne_of_gt (show 0 < u by linarith [hu.1]))
      (Real.log_pos (by norm_num)).ne'
  have hc : ContinuousOn (fun v : ℝ => g (1 + v)) (Icc (0 : ℝ) 1) :=
    hg.comp (by fun_prop) (by intro v hv; constructor <;> linarith [hv.1, hv.2])
  have ht := CycleGeodesic.continuous_leftRiemann_tendsto hc
  have hi : (∫ v in (0 : ℝ)..1, g (1 + v)) = ∫ u, f u ∂dyadicProbabilityMeasure 1 := by
    rw [dyadicProbabilityMeasure_integral (by norm_num : (0 : ℝ) < 1)]
    rw [intervalIntegral.integral_comp_add_left]
    norm_num only [add_zero, one_add_one_eq_two, mul_one]
    simp_rw [g, div_mul_eq_div_div]
    rw [intervalIntegral.integral_div]
  have hsum (n : ℕ) : (∑ k : Fin n, g (1 + (k : ℝ) / n)) =
      ∑ j ∈ Finset.range n, g (cellPoint n j) :=
    Fin.sum_univ_eq_sum_range (fun j => g (cellPoint n j)) n
  simp_rw [hsum, hi] at ht
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let K := |B| + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have herr : ∀ᶠ n : ℕ in atTop,
      |(∑ j ∈ Finset.range n, f (cellPoint n j) * (dyadicProbabilityMeasure 1).real
        (Icc (cellPoint n j) (cellPoint n (j + 1)))) -
        (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, g (cellPoint n j)| ≤
          K / ((n : ℝ) * Real.log 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ Finset.range n,
          |f (cellPoint n j) * (dyadicProbabilityMeasure 1).real
            (Icc (cellPoint n j) (cellPoint n (j + 1))) -
            (1 / (n : ℝ)) * g (cellPoint n j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range n, K * (1 / ((n : ℝ) ^ 2 * Real.log 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        have hb := hB (cellPoint n j) (cellPoint_mem hn hjn.le)
        rw [Real.norm_eq_abs] at hb
        have hfK : |f (cellPoint n j)| ≤ K := by dsimp [K]; linarith [le_abs_self B]
        have he : f (cellPoint n j) * (dyadicProbabilityMeasure 1).real
            (Icc (cellPoint n j) (cellPoint n (j + 1))) -
            (1 / (n : ℝ)) * g (cellPoint n j) =
            f (cellPoint n j) * ((dyadicProbabilityMeasure 1).real
              (Icc (cellPoint n j) (cellPoint n (j + 1))) -
              (1 / (n : ℝ)) / (cellPoint n j * Real.log 2)) := by dsimp [g]; ring
        rw [he, abs_mul, abs_sub_comm]
        exact mul_le_mul hfK (block_weight_error hn hjn) (abs_nonneg _) hK
      _ = K / ((n : ℝ) * Real.log 2) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
  have hz : Tendsto (fun n : ℕ => K / ((n : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat.const_mul (K / Real.log 2)).congr
      (fun n => by ring)
  have hd : Tendsto (fun n : ℕ =>
      (∑ j ∈ Finset.range n, f (cellPoint n j) * (dyadicProbabilityMeasure 1).real
        (Icc (cellPoint n j) (cellPoint n (j + 1)))) -
        (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, g (cellPoint n j)) atTop (𝓝 0) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using herr) hz
  simpa only [sub_add_cancel, zero_add] using hd.add ht

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentBlockTransfer
