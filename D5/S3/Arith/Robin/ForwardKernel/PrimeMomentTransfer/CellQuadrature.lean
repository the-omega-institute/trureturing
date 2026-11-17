/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded variation quadrature for floor sampling with fractional endpoint cells. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.BVCorrelationSummation

/-! Weighted floor sampling and its fractional endpoint corrections. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem p_one_cell (F : ℕ → ℝ) (n : ℕ) :
    (∫ x in (n : ℝ)..(n : ℝ)+1, F ⌊x⌋₊) = F n := by
  calc
    _ = ∫ _x in (n : ℝ)..(n : ℝ)+1, F n := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      intro x hx
      dsimp only
      rw [(Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hx.1.le)).mpr
        ⟨hx.1.le, hx.2⟩]
    _ = _ := by simp

theorem floor_step_intervalIntegrable (F : ℕ → ℝ) (a b : ℝ) (_ha : 0 ≤ a) :
    IntervalIntegrable (fun x => F ⌊x⌋₊) volume a b := by
  let K := ⌊max a b⌋₊
  let C := ∑ n ∈ Finset.range (K + 1), |F n|
  apply (intervalIntegrable_const (c := C)).mono_fun'
    (((measurable_of_countable F).comp Nat.measurable_floor).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hK : ⌊x⌋₊ ≤ K := Nat.floor_le_floor hx.2
  exact (show ‖F ⌊x⌋₊‖ = |F ⌊x⌋₊| from Real.norm_eq_abs _).le.trans
    (Finset.single_le_sum (fun n _ => abs_nonneg (F n))
      (Finset.mem_range.mpr (by omega : ⌊x⌋₊ < K + 1)))

private theorem p_integer_cells (F : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∫ x in (a : ℝ)..(b : ℝ), F ⌊x⌋₊) = ∑ n ∈ Finset.Ico a b, F n := by
  calc
    _ = ∑ n ∈ Finset.Ico a b, ∫ x in (n : ℝ)..((n+1:ℕ) : ℝ), F ⌊x⌋₊ :=
      (intervalIntegral.sum_integral_adjacent_intervals_Ico hab
        (fun n _ => floor_step_intervalIntegrable F _ _ (Nat.cast_nonneg n))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      simpa only [Nat.cast_add, Nat.cast_one] using p_one_cell F n

private theorem p_partial_cell (F : ℕ → ℝ) (y : ℝ) (hy : 0 ≤ y) :
    (∫ x in (⌊y⌋₊ : ℝ)..y, F ⌊x⌋₊) = (y-⌊y⌋₊)*F ⌊y⌋₊ := by
  calc
    _ = ∫ _x in (⌊y⌋₊ : ℝ)..y, F ⌊y⌋₊ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (Nat.floor_le hy)
      intro x hx
      dsimp only
      rw [(Nat.floor_eq_iff ((Nat.cast_nonneg ⌊y⌋₊).trans hx.1.le)).mpr
        ⟨hx.1.le, hx.2.trans (Nat.lt_floor_add_one y)⟩]
    _ = _ := by simp

theorem floor_step_integral (F : ℕ → ℝ) (a : ℕ) (y : ℝ)
    (hay : (a : ℝ) ≤ y) :
    (∫ x in (a : ℝ)..y, F ⌊x⌋₊) =
      (∑ n ∈ Finset.Ico a ⌊y⌋₊, F n)+(y-⌊y⌋₊)*F ⌊y⌋₊ := by
  have hy : 0 ≤ y := (Nat.cast_nonneg a).trans hay
  have haf : a ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).mpr hay
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (floor_step_intervalIntegrable F (a : ℝ) ⌊y⌋₊ (Nat.cast_nonneg a))
    (floor_step_intervalIntegrable F (⌊y⌋₊ : ℝ) y (Nat.cast_nonneg _))
  rw [p_integer_cells F a ⌊y⌋₊ haf, p_partial_cell F y hy] at hi
  exact hi.symm

private theorem p_clipped_integral (N : ℝ) (F : ℕ → ℝ) (y : ℝ)
    (hN : 2 ≤ N) (_hy : (⌊N⌋₊ : ℝ) ≤ y) :
    (∫ x in Ioc (⌊N⌋₊ : ℝ) y,
      (Ioc N (2*N)).indicator (fun t => F ⌊t⌋₊) x) =
      ∫ x in N..max N (min y (2*N)), F ⌊x⌋₊ := by
  have hN0 : 0 ≤ N := by linarith
  rw [setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc,
    max_eq_right (Nat.floor_le hN0)]
  by_cases h : N ≤ min y (2*N)
  · rw [max_eq_right h, intervalIntegral.integral_of_le h]
  · rw [max_eq_left (not_le.mp h).le, intervalIntegral.integral_same,
      Ioc_eq_empty (not_lt.mpr (not_le.mp h).le)]
    simp

private theorem p_clipped_sum (N : ℝ) (F : ℕ → ℝ) (y : ℝ)
    (hN : 2 ≤ N) (hy : (⌊N⌋₊ : ℝ) ≤ y) :
    (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊y⌋₊,
      if N < (n : ℝ) ∧ (n : ℝ) ≤ 2*N then F n else 0) =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊max N (min y (2*N))⌋₊, F n := by
  have hN0 : 0 ≤ N := by linarith
  have hy0 : 0 ≤ y := (Nat.cast_nonneg _).trans hy
  have hyf : ⌊N⌋₊ ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy0).mpr hy
  have hNf : ⌊N⌋₊ ≤ ⌊2*N⌋₊ := Nat.floor_le_floor (by linarith)
  have hflo : ⌊max N (min y (2*N))⌋₊ = min ⌊y⌋₊ ⌊2*N⌋₊ := by
    rw [Nat.floor_mono.map_max, Nat.floor_mono.map_min,
      max_eq_right (le_min hyf hNf)]
  rw [hflo]
  calc
    _ = ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊y⌋₊,
        if n ≤ ⌊2*N⌋₊ then F n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : N < (n : ℝ) := (Nat.floor_lt hN0).mp (Finset.mem_Ioc.mp hn).1
      simp only [hnN, true_and, ← Nat.le_floor_iff (show 0 ≤ 2*N by positivity)]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc, le_min_iff]
      tauto

private theorem p_cell_prefix (N A : ℝ) (F : ℕ → ℝ) (hN : 2 ≤ N) (hA : 0 ≤ A)
    (hF : ∀ n : ℕ, ⌊N⌋₊ ≤ n → n ≤ ⌈2*N⌉₊ → |F n| ≤ A)
    (y : ℝ) (hy : y ∈ Icc (⌊N⌋₊ : ℝ) (⌈2*N⌉₊ : ℝ)) :
    |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊y⌋₊,
        if N < (n : ℝ) ∧ (n : ℝ) ≤ 2*N then F n else 0) -
      ∫ x in Ioc (⌊N⌋₊ : ℝ) y,
        (Ioc N (2*N)).indicator (fun t => F ⌊t⌋₊) x| ≤ 3*A := by
  let z := max N (min y (2*N))
  have hN0 : 0 ≤ N := by linarith
  have hzN : N ≤ z := le_max_left _ _
  have hz0 : 0 ≤ z := hN0.trans hzN
  have hz2 : z ≤ 2*N := max_le (by linarith) (min_le_right _ _)
  have hnf : ⌊N⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor hzN
  have hfc : ⌊z⌋₊ ≤ ⌈2*N⌉₊ :=
    (Nat.floor_le_floor hz2).trans (Nat.floor_le_ceil _)
  have hNc : ⌊N⌋₊ ≤ ⌈2*N⌉₊ := hnf.trans hfc
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (floor_step_intervalIntegrable F (⌊N⌋₊ : ℝ) N (Nat.cast_nonneg _))
    (floor_step_intervalIntegrable F N z hN0)
  rw [p_partial_cell F N hN0,
    floor_step_integral F ⌊N⌋₊ z ((Nat.floor_le hN0).trans hzN)] at hi
  have hs : (∑ n ∈ Finset.Ico ⌊N⌋₊ ⌊z⌋₊, F n) + F ⌊z⌋₊ =
      F ⌊N⌋₊ + ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊z⌋₊, F n :=
    (Finset.sum_Ico_add_eq_sum_Icc (f := F) hnf).trans
      (Finset.add_sum_Ioc_eq_sum_Icc (f := F) hnf).symm
  have he : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊z⌋₊, F n) -
      (∫ x in N..z, F ⌊x⌋₊) =
      (1-(z-⌊z⌋₊))*F ⌊z⌋₊ - (1-(N-⌊N⌋₊))*F ⌊N⌋₊ := by
    linear_combination -hs -hi
  have hcN : 0 ≤ 1-(N-⌊N⌋₊) ∧ 1-(N-⌊N⌋₊) ≤ 1 := by
    constructor <;> linarith [Nat.floor_le hN0, Nat.lt_floor_add_one N]
  have hcz : 0 ≤ 1-(z-⌊z⌋₊) ∧ 1-(z-⌊z⌋₊) ≤ 1 := by
    constructor <;> linarith [Nat.floor_le hz0, Nat.lt_floor_add_one z]
  rw [p_clipped_sum N F y hN hy.1, p_clipped_integral N F y hN hy.1]
  change |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊z⌋₊, F n) - (∫ x in N..z, F ⌊x⌋₊)| ≤ _
  rw [he]
  calc
    _ ≤ |(1-(z-⌊z⌋₊))*F ⌊z⌋₊| + |(1-(N-⌊N⌋₊))*F ⌊N⌋₊| := abs_sub _ _
    _ ≤ A + A := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hcz.1]
        simpa only [one_mul] using
          mul_le_mul hcz.2 (hF _ hnf hfc) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      · rw [abs_mul, abs_of_nonneg hcN.1]
        simpa only [one_mul] using
          mul_le_mul hcN.2 (hF _ le_rfl hNc) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ 3*A := by linarith

/-- Floor sampling and the right endpoint sum differ by at most three times the
uniform sample bound times the supremum-plus-variation bound of the weight. -/
theorem cell_quadrature (N A B : ℝ) (F : ℕ → ℝ) (w : ℝ → ℝ)
    (hN : 2 ≤ N) (hA : 0 ≤ A) (hw : BVBound w B)
    (hF : ∀ n : ℕ, ⌊N⌋₊ ≤ n → n ≤ ⌈2*N⌉₊ → |F n| ≤ A) :
    |(∫ x in N..2*N, w (x/N)*F ⌊x⌋₊)-
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, w ((n : ℝ)/N)*F n)| ≤ 3*A*B := by
  have hN0 : 0 ≤ N := by linarith
  have hNN : N ≤ 2*N := by linarith
  have ha : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le hN0
  have hb : 2*N ≤ (⌈2*N⌉₊ : ℝ) := Nat.le_ceil _
  have habR : (⌊N⌋₊ : ℝ) ≤ (⌈2*N⌉₊ : ℝ) := ha.trans (hNN.trans hb)
  have hab : ⌊N⌋₊ ≤ ⌈2*N⌉₊ := by exact_mod_cast habR
  obtain ⟨U, hU, hbound, hUB⟩ := hw.2.2.2
  let v : ℝ → ℝ := fun x => w (x/N)
  let c : ℕ → ℝ := fun n => if N < (n : ℝ) ∧ (n : ℝ) ≤ 2*N then F n else 0
  let ρ := (Ioc N (2*N)).indicator (fun x => F ⌊x⌋₊)
  have hvar : eVariationOn v univ ≤ eVariationOn w univ :=
    eVariationOn.comp_le_of_monotoneOn w (fun x : ℝ => x/N)
      (fun _ _ _ _ h => div_le_div_of_nonneg_right h hN0)
      (fun _ _ => mem_univ _)
  have hv : BoundedVariationOn v univ := ne_top_of_le_ne_top hw.1 hvar
  have hρ : IntegrableOn ρ (Ioc (⌊N⌋₊ : ℝ) ⌈2*N⌉₊) :=
    (floor_step_intervalIntegrable F (⌊N⌋₊ : ℝ) ⌈2*N⌉₊ (Nat.cast_nonneg _)).1.indicator
      measurableSet_Ioc
  have hm := bv_discrepancy_bound ⌊N⌋₊ ⌈2*N⌉₊ c ρ v (3*A) U
    (eVariationOn w univ).toReal hab (by positivity) hU ENNReal.toReal_nonneg
    hρ hv (hvar.trans_eq (ENNReal.ofReal_toReal hw.1).symm)
    (fun x _ => hbound (x/N)) (p_cell_prefix N A F hN hA hF)
  have hsum : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌈2*N⌉₊, v n*c n) =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, w ((n : ℝ)/N)*F n := by
    change (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌈2*N⌉₊,
      w ((n : ℝ)/N)*(if N < (n : ℝ) ∧ (n : ℝ) ≤ 2*N then F n else 0)) = _
    simp_rw [mul_ite, mul_zero]
    simpa only [Nat.floor_natCast, min_eq_right hb, max_eq_right hNN] using
      p_clipped_sum N (fun n => w ((n : ℝ)/N)*F n) (⌈2*N⌉₊ : ℝ) hN habR
  have hint : (∫ x in Ioc (⌊N⌋₊ : ℝ) ⌈2*N⌉₊, v x*ρ x) =
      ∫ x in N..2*N, w (x/N)*F ⌊x⌋₊ := by
    have heq : (fun x => v x*ρ x) =
        (Ioc N (2*N)).indicator (fun x => w (x/N)*F ⌊x⌋₊) := by
      funext x
      by_cases hx : x ∈ Ioc N (2*N) <;> simp [v, ρ, hx]
    rw [heq, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (Ioc_subset_Ioc ha hb)]
    exact (intervalIntegral.integral_of_le hNN).symm
  rw [hsum, hint, abs_sub_comm] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hUB (by positivity))

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
