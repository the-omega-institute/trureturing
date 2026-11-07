/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthCells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cell limits and monotone rectangles determine the moving-length constant. -/

import D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Equal cells of the interval [1,2] and their triangular mean-square limits. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs

noncomputable section

/-- The left endpoint of the j-th equal cell of [1,2]. -/
def cellPoint (n j : ℕ) : ℝ := 1 + (j : ℝ) / n

/-- The mean square obtained by freezing the length at each left endpoint. -/
def cellMeanSquare (E : ℝ → ℝ) (n : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
    triangularAverage E (fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X) x ^ 2

/-- The limiting normalized mean square for the n-cell approximation. -/
def cellConstant (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, cellPoint n j ^ (-4 / 5 : ℝ)) / (15 * n)

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

private lemma fixed_normalizer_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X => (X / fixedLength c X * lengthLog c X) / meanSquareScale X)
      atTop (𝓝 (1 / (5 * c))) := by
  have hz : Tendsto (fun X : ℝ => Real.log c / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := ((tendsto_const_nhds (x := (1 / 5 : ℝ))).sub hz).div_const c
  norm_num only [sub_zero] at h
  convert h.congr' (show ∀ᶠ X : ℝ in atTop,
      ((1 / 5 : ℝ) - Real.log c / Real.log X) / c =
      (X / fixedLength c X * lengthLog c X) / meanSquareScale X from ?_) using 1
  · congr 1
    ring
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := by linarith
  have hL : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hp : X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) = X := by
    rw [← Real.rpow_add hX0]
    norm_num
  have hl : lengthLog c X = (1 / 5 : ℝ) * Real.log X - Real.log c := by
    rw [lengthLog, Real.log_div hX0.ne' (by dsimp [fixedLength]; positivity),
      fixedLength, Real.log_mul hc.ne' (Real.rpow_pos_of_pos hX0 _).ne',
      Real.log_rpow hX0]
    ring
  rw [hl]
  dsimp [fixedLength, meanSquareScale]
  field_simp
  linear_combination (Real.log X - 5 * Real.log c) * hp

/-- Fixed-length limits on each cell add to the normalized cell mean-square limit. -/
theorem cell_mean_square_tendsto
    {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hSV : ShortIntervalMeanSquareBoundFor E)
    (hGM : CumulativeVarianceBandAsymptoticFor E)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun X => cellMeanSquare E n X / meanSquareScale X)
      atTop (𝓝 (cellConstant n)) := by
  have hj (j : ℕ) (hj : j ∈ Finset.range n) :
      Tendsto (fun X =>
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
          triangularAverage E (fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X) x ^ 2) /
            meanSquareScale X)
        atTop (𝓝 (cellPoint n j ^ (-4 / 5 : ℝ) / (15 * n))) := by
    have hjn := Finset.mem_range.mp hj
    have ha := cellPoint_mem hn hjn.le
    have hb := cellPoint_mem hn (Nat.succ_le_of_lt hjn)
    have hc : 0 < cellPoint n j ^ (4 / 5 : ℝ) :=
      Real.rpow_pos_of_pos (by linarith [ha.1]) _
    have ht := (TriangularMeanSquare.fixed_length_triangular_mean_square_tendsto
      hE hSV hGM ha.1 (cellPoint_lt hn j) hb.2 hc).mul
      (fixed_normalizer_ratio hc)
    have he : (cellPoint n (j + 1) - cellPoint n j) / 3 *
        (1 / (5 * cellPoint n j ^ (4 / 5 : ℝ))) =
        cellPoint n j ^ (-4 / 5 : ℝ) / (15 * n) := by
      rw [cellPoint_step hn, show (-4 / 5 : ℝ) = -(4 / 5 : ℝ) by norm_num,
        Real.rpow_neg (by linarith [ha.1] : 0 ≤ cellPoint n j)]
      ring
    rw [he] at ht
    apply ht.congr'
    have hz : ∀ᶠ X : ℝ in atTop, X / fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X *
        lengthLog (cellPoint n j ^ (4 / 5 : ℝ)) X ≠ 0 := by
      have ht' := (fixed_normalizer_ratio hc).eventually
        (lt_mem_nhds (by positivity : (0 : ℝ) < 1 / (5 * cellPoint n j ^ (4 / 5 : ℝ))))
      filter_upwards [ht'] with X hX
      exact (div_ne_zero_iff.mp hX.ne').1
    filter_upwards [hz] with X hX
    exact div_mul_div_cancel₀ hX
  have ht := tendsto_finsetSum (Finset.range n) hj
  simpa only [cellMeanSquare, cellConstant, Finset.sum_div] using ht

/-- Monotone rectangles squeeze the cell constant with an error at most 1/(15n). -/
private theorem cell_constant_bounds {n : ℕ} (hn : 0 < n) :
    ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3 ≤ cellConstant n ∧
    cellConstant n ≤ ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3 + 1 / (15 * n) := by
  let f : ℝ → ℝ := fun v => v ^ (-4 / 5 : ℝ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi (j : ℕ) (_hj : j < n) : IntervalIntegrable f volume
      (cellPoint n j) (cellPoint n (j + 1)) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -4 / 5)
  have hs : (∑ j ∈ Finset.range n, ∫ v in (cellPoint n j)..(cellPoint n (j + 1)), f v) =
      ∫ v in (1 : ℝ)..2, f v := by
    convert intervalIntegral.sum_integral_adjacent_intervals hi using 1 <;>
      norm_num [cellPoint, hn.ne', f]
  have hu (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫ v in (cellPoint n j)..(cellPoint n (j + 1)), f v) ≤
        f (cellPoint n j) / n := by
    have hjn := Finset.mem_range.mp hj
    have hle := (cellPoint_lt hn j).le
    calc
      _ ≤ ∫ _v in (cellPoint n j)..(cellPoint n (j + 1)), f (cellPoint n j) := by
        apply intervalIntegral.integral_mono_on hle (hi j hjn) (intervalIntegrable_const)
        intro v hv
        exact Real.rpow_le_rpow_of_nonpos
          (by linarith [(cellPoint_mem hn hjn.le).1]) hv.1 (by norm_num)
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
          (by linarith [(cellPoint_mem hn hjn.le).1, hv.1]) hv.2 (by norm_num)
  have hu' := Finset.sum_le_sum hu
  have hl' := Finset.sum_le_sum hl
  rw [hs] at hu' hl'
  have ht : (∑ j ∈ Finset.range n, f (cellPoint n j)) -
      (∑ j ∈ Finset.range n, f (cellPoint n (j + 1))) = 1 - f 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub']
    norm_num [cellPoint, hn.ne', f]
  have hv : (∫ v in (1 : ℝ)..2, f v) =
      5 * ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) := by
    dsimp [f]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -4 / 5))]
    norm_num
    ring
  rw [← Finset.sum_div] at hu' hl'
  rw [hv] at hu' hl'
  dsimp [cellConstant]
  change _ ≤ (∑ j ∈ Finset.range n, f (cellPoint n j)) / (15 * n) ∧ _
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 15 * n)).mpr
    have h := (le_div_iff₀ hn').mp hu'
    nlinarith
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 15 * n)).mpr
    have h := (div_le_iff₀ hn').mp hl'
    have hf2 : 0 ≤ f 2 := Real.rpow_nonneg (by norm_num) _
    have hnz : (n : ℝ) ≠ 0 := hn'.ne'
    have he : 1 / (15 * (n : ℝ)) * (15 * n) = 1 := by field_simp
    change (∑ j ∈ Finset.range n, f (cellPoint n j)) ≤ _
    nlinarith

/-- The constants of the equal-cell approximations converge to the moving-length constant. -/
theorem cell_constant_tendsto :
    Tendsto cellConstant atTop (𝓝 (((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3)) := by
  have hz : Tendsto (fun n : ℕ => 1 / (15 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hb : ∀ᶠ n : ℕ in atTop,
      |cellConstant n - ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3| ≤ 1 / (15 * n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    obtain ⟨hl, hu⟩ := cell_constant_bounds hn
    rw [abs_of_nonneg (sub_nonneg.mpr hl)]
    linarith
  have ht : Tendsto (fun n => cellConstant n - ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3)
      atTop (𝓝 0) := squeeze_zero_norm' hb hz
  simpa using ht.add_const (((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3)

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells
