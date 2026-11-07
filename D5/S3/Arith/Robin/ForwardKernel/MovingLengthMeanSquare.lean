/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal-cell freezing transfers triangular mean squares to moving lengths. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance

/-! The equal-cell comparison for a triangular average of length x^(4/5). -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthMeanSquare

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs VarianceTransfer MovingLengthCells
open MovingLengthRegularity MovingLengthVariance

noncomputable section

private lemma power_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    b ^ (4 / 5 : ℝ) - a ^ (4 / 5 : ℝ) ≤ b - a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hdiv : 1 ≤ b / a := (one_le_div ha0).mpr hab
  have hr := Real.rpow_le_self_of_one_le hdiv (by norm_num : (4 / 5 : ℝ) ≤ 1)
  have ha' := Real.rpow_le_self_of_one_le ha (by norm_num : (4 / 5 : ℝ) ≤ 1)
  have he : b ^ (4 / 5 : ℝ) = a ^ (4 / 5 : ℝ) * (b / a) ^ (4 / 5 : ℝ) := by
    rw [Real.div_rpow hb0.le ha0.le]
    field_simp
  calc
    _ ≤ a ^ (4 / 5 : ℝ) * (b / a - 1) := by rw [he]; nlinarith [Real.rpow_nonneg ha0.le (4 / 5 : ℝ)]
    _ ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_right ha' (by linarith)
    _ = _ := by field_simp <;> ring

private lemma cell_length_bounds {n j : ℕ} (hn : 0 < n) (hj : j < n)
    {X x : ℝ} (hX : 0 < X)
    (hx : x ∈ Icc (cellPoint n j * X) (cellPoint n (j + 1) * X)) :
    let h := fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X
    X ^ (4 / 5 : ℝ) ≤ h ∧ h ≤ 2 * X ^ (4 / 5 : ℝ) ∧
      x ^ (4 / 5 : ℝ) ∈ Icc h (h + X ^ (4 / 5 : ℝ) / n) := by
  have ha := cellPoint_mem hn hj.le
  have hb := cellPoint_mem hn (Nat.succ_le_of_lt hj)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hH : 0 < X ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hX _
  have hv : x / X ∈ Icc (cellPoint n j) (cellPoint n (j + 1)) :=
    ⟨(le_div_iff₀ hX).mpr hx.1, (div_le_iff₀ hX).mpr hx.2⟩
  have hv0 : 0 < x / X := by linarith [hv.1, ha.1]
  have he : x ^ (4 / 5 : ℝ) = (x / X) ^ (4 / 5 : ℝ) * X ^ (4 / 5 : ℝ) := by
    rw [Real.div_rpow (by nlinarith [hx.1, ha.1] : 0 ≤ x) hX.le]
    exact (div_mul_cancel₀ _ hH.ne').symm
  have hu := power_sub_le ha.1 hv.1
  have hstep := cellPoint_step hn j
  have ha0 : 0 < cellPoint n j := by linarith [ha.1]
  have hmono := Real.rpow_le_rpow ha0.le hv.1 (by norm_num : (0 : ℝ) ≤ 4 / 5)
  dsimp only [fixedLength]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_mul_of_one_le_left hH.le (Real.one_le_rpow ha.1 (by norm_num))
  · exact mul_le_mul_of_nonneg_right
      ((Real.rpow_le_self_of_one_le ha.1 (by norm_num)).trans ha.2) hH.le
  · rw [he]
    exact mul_le_mul_of_nonneg_right hmono hH.le
  · rw [he]
    have hvstep : x / X - cellPoint n j ≤ 1 / (n : ℝ) := by linarith [hv.2]
    have h := mul_le_mul_of_nonneg_right (hu.trans hvstep) hH.le
    linear_combination h

private def cellSquareError (E : ℝ → ℝ) (n : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
    (triangularAverage E (x ^ (4 / 5 : ℝ)) x -
      triangularAverage E (fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X) x) ^ 2

private lemma moving_square_intervalIntegrable {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2)
      volume a b := by
  have hm : Measurable (fun x : ℝ => x ^ (4 / 5 : ℝ)) := by fun_prop
  have hf := triangularAverage_variable_memLp hE hm hab (Real.rpow_pos_of_pos ha (4 / 5 : ℝ))
    (L := b ^ (4 / 5 : ℝ)) (fun x hx =>
      ⟨Real.rpow_le_rpow ha.le hx.1 (by norm_num),
        Real.rpow_le_rpow (ha.le.trans hx.1) hx.2 (by norm_num)⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf

private lemma cell_square_error_le {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {n : ℕ} (hn : 0 < n) {X : ℝ} (hX : 1 < X)
    (hV : ∀ u ∈ Icc (X ^ (4 / 5 : ℝ)) (4 * X ^ (4 / 5 : ℝ)),
      (∫ x in X..(2 * X), increment E u x ^ 2) ≤
        32 * X * X ^ (4 / 5 : ℝ) * Real.log X) :
    cellSquareError E n X ≤ 18 / (n : ℝ) ^ 2 * cellMeanSquare E n X +
      64 / n * meanSquareScale X := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX0 : 0 < X := by linarith
  have hH : 0 < X ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hL : 0 < Real.log X := Real.log_pos hX
  have hp : X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) = X := by
    rw [← Real.rpow_add hX0]; norm_num
  have hj (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
        (triangularAverage E (x ^ (4 / 5 : ℝ)) x -
          triangularAverage E (fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X) x) ^ 2) ≤
        18 / (n : ℝ) ^ 2 *
          (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
            triangularAverage E (fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X) x ^ 2) +
          64 / (n : ℝ) ^ 2 * meanSquareScale X := by
    have hjn := Finset.mem_range.mp hj
    let h := fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X
    let d := X ^ (4 / 5 : ℝ) / n
    have ha := cellPoint_mem hn hjn.le
    have hb := cellPoint_mem hn (Nat.succ_le_of_lt hjn)
    have hab : cellPoint n j * X ≤ cellPoint n (j + 1) * X :=
      mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le
    have hh := cell_length_bounds hn hjn hX0 (x := cellPoint n j * X) ⟨le_rfl, hab⟩
    have hh0 : 0 < h := hH.trans_le hh.1
    have hd0 : 0 ≤ d := by dsimp [d]; positivity
    have hdh : d ≤ h := (div_le_self hH.le hn1).trans hh.1
    have hhm : Measurable (fun x : ℝ => x ^ (4 / 5 : ℝ)) := by fun_prop
    have hbound (x : ℝ) (hx : x ∈ Icc (cellPoint n j * X) (cellPoint n (j + 1) * X)) :=
      (cell_length_bounds hn hjn hX0 hx).2.2
    have hVc (u : ℝ) (hu : u ∈ Icc h (h + d)) :
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X), increment E u x ^ 2) ≤
          32 * X * X ^ (4 / 5 : ℝ) * Real.log X := by
      have hi : IntervalIntegrable (fun x => increment E u x ^ 2) volume X (2 * X) := by
        simpa only [pow_two, Pi.mul_apply, id_eq] using
          (increment_product_comp_integrableOn hE isCompact_uIcc
            continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
      apply le_trans (intervalIntegral.integral_mono_interval
        (by nlinarith [ha.1] : X ≤ cellPoint n j * X) hab
        (by nlinarith [hb.2] : cellPoint n (j + 1) * X ≤ 2 * X)
        (Eventually.of_forall (fun _ => sq_nonneg _)) hi)
      apply hV u
      refine ⟨hh.1.trans hu.1, ?_⟩
      have hdH : d ≤ X ^ (4 / 5 : ℝ) := div_le_self hH.le hn1
      linarith [hu.2, hh.2.1]
    have ht := variable_average_square_error_le hE hhm hab hh0 hd0 hdh hbound hVc
    have hratio : d / h ≤ 1 / (n : ℝ) := by
      dsimp [d]
      rw [div_right_comm]
      exact div_le_div_of_nonneg_right ((div_le_one hh0).mpr hh.1) hn'.le
    have hmass0 : 0 ≤ ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
        triangularAverage E h x ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
    have hfirst : 18 * (d / h) ^ 2 *
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X), triangularAverage E h x ^ 2) ≤
        18 / (n : ℝ) ^ 2 *
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X), triangularAverage E h x ^ 2) := by
      have ht := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio 2) hmass0
      convert mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 18) using 1 <;> ring
    have hsecond : 2 * d ^ 2 / h ^ 4 * (32 * X * X ^ (4 / 5 : ℝ) * Real.log X) ≤
        64 / (n : ℝ) ^ 2 * meanSquareScale X := by
      calc
        _ ≤ 2 * d ^ 2 / (X ^ (4 / 5 : ℝ)) ^ 4 *
            (32 * X * X ^ (4 / 5 : ℝ) * Real.log X) := by
          gcongr
          exact hh.1
        _ = _ := by
          dsimp [d, meanSquareScale]
          field_simp
          nlinarith [hp]
    exact ht.trans (add_le_add hfirst hsecond)
  have ht := Finset.sum_le_sum hj
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at ht
  convert ht using 1 <;> dsimp [cellSquareError, cellMeanSquare]
  congr 1
  field_simp

private lemma interval_square_comparison {a b t : ℝ} (hab : a ≤ b) (ht : 0 < t)
    {f g : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, f x ^ 2) ≤ (1 + t) * (∫ x in a..b, g x ^ 2) +
      (1 + 1 / t) * (∫ x in a..b, (f x - g x) ^ 2) := by
  have hF : 0 ≤ ∫ x in a..b, f x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  have hG : 0 ≤ ∫ x in a..b, g x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  have hD : 0 ≤ ∫ x in a..b, (f x - g x) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  have hr := interval_l2_reverse_triangle hab hf hg
  have hnorm : Real.sqrt (∫ x in a..b, f x ^ 2) ≤
      Real.sqrt (∫ x in a..b, g x ^ 2) + Real.sqrt (∫ x in a..b, (f x - g x) ^ 2) := by
    linarith [(abs_le.mp hr).2]
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  have hy := two_mul_le_add_mul_sq
    (a := Real.sqrt (∫ x in a..b, g x ^ 2))
    (b := Real.sqrt (∫ x in a..b, (f x - g x) ^ 2)) ht
  rw [add_sq, Real.sq_sqrt hF, Real.sq_sqrt hG, Real.sq_sqrt hD] at hs
  rw [Real.sq_sqrt hG, Real.sq_sqrt hD, inv_eq_one_div] at hy
  nlinarith

private lemma cell_square_comparison {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {n : ℕ} (hn : 0 < n) {X t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    (∫ x in X..(2 * X), triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2) ≤
        (1 + t) * cellMeanSquare E n X + (1 + 1 / t) * cellSquareError E n X ∧
    cellMeanSquare E n X ≤
        (1 + t) * (∫ x in X..(2 * X), triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2) +
          (1 + 1 / t) * cellSquareError E n X := by
  have hm : Measurable (fun x : ℝ => x ^ (4 / 5 : ℝ)) := by fun_prop
  have hh (j : ℕ) (hj : j < n) := by
    have hab := mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX.le
    have ha := cellPoint_mem hn hj.le
    have h0 : 0 < fixedLength (cellPoint n j ^ (4 / 5 : ℝ)) X := by
      dsimp [fixedLength]
      exact mul_pos (Real.rpow_pos_of_pos (by linarith [ha.1]) _) (Real.rpow_pos_of_pos hX _)
    have hf := triangularAverage_variable_memLp hE hm hab h0
      (fun x hx => (cell_length_bounds hn hj hX hx).2.2)
    have hg := triangularAverage_variable_memLp hE measurable_const hab h0
      (fun _ _ => ⟨le_rfl, le_rfl⟩)
    exact And.intro (interval_square_comparison hab ht hf hg) (interval_square_comparison hab ht hg hf)
  have hs : (∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
      triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2) =
      ∫ x in X..(2 * X), triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2 := by
    have hi (j : ℕ) (hj : j < n) : IntervalIntegrable
        (fun x => triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2)
        volume (cellPoint n j * X) (cellPoint n (j + 1) * X) :=
      moving_square_intervalIntegrable hE (by nlinarith [(cellPoint_mem hn hj.le).1])
        (mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX.le)
    convert intervalIntegral.sum_integral_adjacent_intervals hi using 1 <;>
      norm_num [cellPoint, hn.ne']
  have hu := Finset.sum_le_sum (fun j hj => (hh j (Finset.mem_range.mp hj)).1)
  have hl := Finset.sum_le_sum (fun j hj => (hh j (Finset.mem_range.mp hj)).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hu hl
  rw [hs] at hu hl
  constructor
  · exact hu
  · simpa only [cellMeanSquare, cellSquareError, sub_sq_comm] using hl

/-- The short-interval bound and uniform variance band imply the moving-length mean-square limit. -/
theorem moving_length_mean_square_tendsto
    {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hSV : ShortIntervalMeanSquareBoundFor E)
    (hGM : CumulativeVarianceBandAsymptoticFor E) :
    Filter.Tendsto
      (fun X =>
        (∫ x in X..(2 * X),
          triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2) /
          meanSquareScale X)
      Filter.atTop
      (nhds (((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3)) := by
  let C : ℝ := ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr (Real.one_le_rpow
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 5))) (by norm_num)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := min (ε / 8) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδe : δ ≤ ε / 8 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  let t : ℝ := ε / (8 * (C + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have htC : t * (C + 1) = ε / 8 := by dsimp [t]; field_simp
  let k : ℝ := 1 + 1 / t
  have hk : 0 < k := by dsimp [k]; positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hn2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hnat
  have herror : Tendsto (fun n : ℕ =>
      k * (18 / (n : ℝ) ^ 2 * (C + 1) + 64 / n)) atTop (nhds 0) := by
    have h1 := (tendsto_const_nhds (x := (18 : ℝ))).div_atTop hn2
    have h2 := (tendsto_const_nhds (x := (64 : ℝ))).div_atTop hnat
    simpa using ((h1.mul_const (C + 1)).add h2).const_mul k
  obtain ⟨n, hn, hCn, hne⟩ := (eventually_gt_atTop (0 : ℕ) |>.and
    ((Metric.tendsto_nhds.mp cell_constant_tendsto δ hδ).and
      (herror.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))))).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hCn' : |cellConstant n - C| < δ := by simpa only [Real.dist_eq] using hCn
  have hQ := Metric.tendsto_nhds.mp (cell_mean_square_tendsto hE hSV hGM hn) δ hδ
  filter_upwards [eventually_gt_atTop (1 : ℝ), moving_strip_variance_bound hE hGM, hQ]
    with X hX hV hQ
  have hX0 : 0 < X := by linarith
  have hS : 0 < meanSquareScale X :=
    mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)
  let A : ℝ := (∫ x in X..(2 * X), triangularAverage E (x ^ (4 / 5 : ℝ)) x ^ 2) /
    meanSquareScale X
  let B : ℝ := cellMeanSquare E n X / meanSquareScale X
  let R : ℝ := cellSquareError E n X / meanSquareScale X
  have hB : |B - C| < 2 * δ := by
    have hB' : |B - cellConstant n| < δ := by simpa only [Real.dist_eq] using hQ
    have hh := abs_add_le (B - cellConstant n) (cellConstant n - C)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hBC : B ≤ C + 1 := by linarith [(abs_lt.mp hB).2]
  have hRC : k * R < ε / 4 := by
    have hr := div_le_div_of_nonneg_right (cell_square_error_le hE hn hX hV) hS.le
    have hr' : R ≤ 18 / (n : ℝ) ^ 2 * B + 64 / n := by
      dsimp [R, B]
      convert hr using 1 <;> field_simp <;> ring
    have hbound : R ≤ 18 / (n : ℝ) ^ 2 * (C + 1) + 64 / n :=
      hr'.trans (add_le_add (mul_le_mul_of_nonneg_left hBC
        (by positivity : (0 : ℝ) ≤ 18 / (n : ℝ) ^ 2)) (le_refl (64 / (n : ℝ))))
    exact (mul_le_mul_of_nonneg_left hbound hk.le).trans_lt hne
  obtain ⟨hU, hD⟩ := cell_square_comparison hE hn hX0 ht
  have hU' : A ≤ (1 + t) * B + k * R := by
    have hh := div_le_div_of_nonneg_right hU hS.le
    dsimp [A, B, R, k]
    convert hh using 1 <;> ring
  have hD' : B ≤ (1 + t) * A + k * R := by
    have hh := div_le_div_of_nonneg_right hD hS.le
    dsimp [A, B, R, k]
    convert hh using 1 <;> ring
  change |A - C| < ε
  rw [abs_lt]
  constructor
  · have hlow := (abs_lt.mp hB).1
    have htC' : t * C ≤ ε / 8 := by nlinarith
    nlinarith [mul_pos ht hε]
  · have hupp := (abs_lt.mp hB).2
    have htB : t * B ≤ ε / 8 := by nlinarith [mul_le_mul_of_nonneg_left hBC ht.le]
    nlinarith

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthMeanSquare
