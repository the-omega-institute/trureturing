/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthCells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cell limits and monotone rectangles determine the moving-length constant. -/

import D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Equal cells of the interval [1,2] and their profile mean-square limits. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs

noncomputable section

/-- The left endpoint of the j-th equal cell of [1,2]. -/
def cellPoint (n j : ℕ) : ℝ := 1 + (j : ℝ) / n

/-- The mean square obtained by freezing the length at each left endpoint. -/
def cellMeanSquare (E : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ) (n : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
    profileAverage E g (fixedLength θ (cellPoint n j ^ θ) X) x ^ 2

/-- The limiting normalized mean square for the n-cell approximation. -/
def cellConstant (θ : ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((1 - θ) * Q g / (n : ℝ)) *
    ∑ j ∈ Finset.range n, cellPoint n j ^ (-θ)

theorem cellPoint_mem {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    cellPoint n j ∈ Icc (1 : ℝ) 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [cellPoint]
  constructor
  · have : (0 : ℝ) ≤ (j : ℝ) / n := by positivity
    linarith
  · have : (j : ℝ) / n ≤ 1 := (div_le_one hn').mpr (by exact_mod_cast hj)
    linarith

theorem cellPoint_step {n : ℕ} (hn : 0 < n) (j : ℕ) :
    cellPoint n (j + 1) - cellPoint n j = 1 / (n : ℝ) := by
  dsimp [cellPoint]
  push_cast
  ring

theorem cellPoint_lt {n : ℕ} (hn : 0 < n) (j : ℕ) :
    cellPoint n j < cellPoint n (j + 1) := by
  have h := cellPoint_step hn j
  have : (0 : ℝ) < n := by exact_mod_cast hn
  linarith [one_div_pos.mpr this]

private lemma fixed_normalizer_ratio {θ c : ℝ} (hc : 0 < c) :
    Tendsto (fun X => (X / fixedLength θ c X * lengthLog θ c X) / meanSquareScale θ X)
      atTop (𝓝 ((1 - θ) / c)) := by
  have hz : Tendsto (fun X : ℝ => Real.log c / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := ((tendsto_const_nhds (x := 1 - θ)).sub hz).div_const c
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hp : X ^ θ * X ^ (1 - θ) = X := by
    rw [← Real.rpow_add hX0, add_sub_cancel, Real.rpow_one]
  have hl : lengthLog θ c X = (1 - θ) * Real.log X - Real.log c := by
    rw [lengthLog, Real.log_div hX0.ne' (by dsimp [fixedLength]; positivity),
      fixedLength, Real.log_mul hc.ne' (Real.rpow_pos_of_pos hX0 _).ne',
      Real.log_rpow hX0]
    ring
  rw [hl]
  dsimp [fixedLength, meanSquareScale]
  field_simp [(Real.log_pos hX).ne']
  linear_combination (Real.log X - θ * Real.log X - Real.log c) * hp

/-- Fixed-length profile limits on each cell add to the normalized cell mean-square limit. -/
theorem cell_mean_square_tendsto
    {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {g : ℝ → ℝ} (hg : ProfileIntegrable g)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun X => cellMeanSquare E θ g n X / meanSquareScale θ X)
      atTop (𝓝 (cellConstant θ g n)) := by
  have hθ : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hj (j : ℕ) (hj : j ∈ Finset.range n) :
      Tendsto (fun X =>
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
          profileAverage E g (fixedLength θ (cellPoint n j ^ θ) X) x ^ 2) /
            meanSquareScale θ X)
        atTop (𝓝 (((1 - θ) * Q g / (n : ℝ)) * cellPoint n j ^ (-θ))) := by
    have hjn := Finset.mem_range.mp hj
    have ha := cellPoint_mem hn hjn.le
    have hb := cellPoint_mem hn (Nat.succ_le_of_lt hjn)
    have hc : 0 < cellPoint n j ^ θ :=
      Real.rpow_pos_of_pos (by linarith [ha.1]) _
    have ht := (TriangularMeanSquare.fixed_length_profile_mean_square_tendsto
      hE hB hV hg ha.1 (cellPoint_lt hn j) hb.2 hc).mul
      (fixed_normalizer_ratio (θ := θ) hc)
    have he : ((cellPoint n (j + 1) - cellPoint n j) * Q g) *
        ((1 - θ) / cellPoint n j ^ θ) =
        ((1 - θ) * Q g / (n : ℝ)) * cellPoint n j ^ (-θ) := by
      rw [cellPoint_step hn, Real.rpow_neg (by linarith [ha.1] : 0 ≤ cellPoint n j)]
      ring
    rw [he] at ht
    apply ht.congr'
    have hz : ∀ᶠ X : ℝ in atTop,
        X / fixedLength θ (cellPoint n j ^ θ) X *
          lengthLog θ (cellPoint n j ^ θ) X ≠ 0 := by
      have ht' := (fixed_normalizer_ratio (θ := θ) hc).eventually
        (lt_mem_nhds (div_pos (sub_pos.mpr hθ) hc))
      filter_upwards [ht'] with X hX
      exact (div_ne_zero_iff.mp hX.ne').1
    filter_upwards [hz] with X hX
    exact div_mul_div_cancel₀ hX
  have ht := tendsto_finsetSum (Finset.range n) hj
  simpa only [cellMeanSquare, cellConstant, Finset.sum_div, Finset.mul_sum] using ht

private theorem rectangle_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {n : ℕ} (hn : 0 < n) :
    (∫ v in (1 : ℝ)..2, v ^ (-θ)) ≤
        (∑ j ∈ Finset.range n, cellPoint n j ^ (-θ)) / n ∧
      (∑ j ∈ Finset.range n, cellPoint n j ^ (-θ)) / n ≤
        (∫ v in (1 : ℝ)..2, v ^ (-θ)) + 1 / n := by
  let f : ℝ → ℝ := fun v => v ^ (-θ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi (j : ℕ) (_hj : j < n) : IntervalIntegrable f volume
      (cellPoint n j) (cellPoint n (j + 1)) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -θ)
  have hs : (∑ j ∈ Finset.range n, ∫ v in (cellPoint n j)..(cellPoint n (j + 1)), f v) =
      ∫ v in (1 : ℝ)..2, f v := by
    convert intervalIntegral.sum_integral_adjacent_intervals hi using 1 <;>
      norm_num [cellPoint, hn.ne', f]
  have hu (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫ v in (cellPoint n j)..(cellPoint n (j + 1)), f v) ≤
        f (cellPoint n j) / n := by
    have hjn := Finset.mem_range.mp hj
    calc
      _ ≤ ∫ _v in (cellPoint n j)..(cellPoint n (j + 1)), f (cellPoint n j) := by
        apply intervalIntegral.integral_mono_on (cellPoint_lt hn j).le
          (hi j hjn) intervalIntegrable_const
        intro v hv
        exact Real.rpow_le_rpow_of_nonpos
          (by linarith [(cellPoint_mem hn hjn.le).1]) hv.1 (by linarith)
      _ = _ := by
        rw [intervalIntegral.integral_const, smul_eq_mul, cellPoint_step hn]
        ring
  have hl (j : ℕ) (hj : j ∈ Finset.range n) :
      f (cellPoint n (j + 1)) / n ≤
        ∫ v in (cellPoint n j)..(cellPoint n (j + 1)), f v := by
    have hjn := Finset.mem_range.mp hj
    calc
      _ = ∫ _v in (cellPoint n j)..(cellPoint n (j + 1)), f (cellPoint n (j + 1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, cellPoint_step hn]
        ring
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on (cellPoint_lt hn j).le
          intervalIntegrable_const (hi j hjn)
        intro v hv
        exact Real.rpow_le_rpow_of_nonpos
          (by linarith [(cellPoint_mem hn hjn.le).1, hv.1]) hv.2 (by linarith)
  have hu' := Finset.sum_le_sum hu
  have hl' := Finset.sum_le_sum hl
  rw [hs, ← Finset.sum_div] at hu' hl'
  have ht : (∑ j ∈ Finset.range n, f (cellPoint n j)) -
      (∑ j ∈ Finset.range n, f (cellPoint n (j + 1))) = 1 - f 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub']
    norm_num [cellPoint, hn.ne', f]
  refine ⟨hu', ?_⟩
  apply (div_le_iff₀ hn').mpr
  have h := (div_le_iff₀ hn').mp hl'
  have hf2 : 0 ≤ f 2 := Real.rpow_nonneg (by norm_num) _
  rw [add_mul, one_div_mul_cancel hn'.ne']
  change (∑ j ∈ Finset.range n, f (cellPoint n j)) ≤ _
  linarith

/-- The cell constants converge to the profile energy times the moving-length factor. -/
theorem cell_constant_tendsto {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (g : ℝ → ℝ) :
    Tendsto (cellConstant θ g) atTop
      (𝓝 (Q g * ((2 : ℝ) ^ (1 - θ) - 1))) := by
  let I := ∫ v in (1 : ℝ)..2, v ^ (-θ)
  have hz : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ n : ℕ in atTop,
      |(∑ j ∈ Finset.range n, cellPoint n j ^ (-θ)) / n - I| ≤ 1 / n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    obtain ⟨hl, hu⟩ := rectangle_bounds hθ0 hθ1 hn
    rw [abs_of_nonneg (sub_nonneg.mpr hl)]
    linarith
  have ht : Tendsto (fun n =>
      (∑ j ∈ Finset.range n, cellPoint n j ^ (-θ)) / n - I)
      atTop (𝓝 0) := squeeze_zero_norm' hb hz
  have ht' := (ht.add_const I).const_mul ((1 - θ) * Q g)
  simp only [sub_add_cancel, zero_add] at ht'
  have hv : I = ((2 : ℝ) ^ (1 - θ) - 1) / (1 - θ) := by
    dsimp [I]
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -θ))]
    rw [show -θ + 1 = 1 - θ by ring, Real.one_rpow]
  have he : (1 - θ) * Q g * I = Q g * ((2 : ℝ) ^ (1 - θ) - 1) := by
    rw [hv]
    field_simp
  rw [he] at ht'
  convert ht' using 1
  funext n
  dsimp [cellConstant]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells
