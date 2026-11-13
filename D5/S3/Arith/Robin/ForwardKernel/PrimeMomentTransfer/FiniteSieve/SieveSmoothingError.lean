/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothingError
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothingError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive shift averages approximate sharp sieve intervals in the fourth norm. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveEndpointFourth
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveSmoothKernel
import Mathlib.Analysis.Convex.Integral

/-! Averaging translated sharp intervals controls the fourth norm of the smoothing error. -/

open scoped BigOperators Topology NNReal ENNReal
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem weighted_jensen_fourth (w g : ℝ → ℝ)
    (hw : Integrable w) (hw0 : ∀ r, 0 ≤ w r) (hw1 : (∫ r, w r) = 1)
    (hg : Integrable (fun r => w r * g r))
    (hg4 : Integrable (fun r => w r * |g r| ^ 4)) :
    |∫ r, w r * g r| ^ 4 ≤ ∫ r, w r * |g r| ^ 4 := by
  let v : ℝ → ℝ≥0 := fun r => ⟨w r, hw0 r⟩
  have hv : AEMeasurable v volume := hw.aestronglyMeasurable.aemeasurable.subtype_mk
  let ν := volume.withDensity (fun r => (v r : ℝ≥0∞))
  have hν : IsProbabilityMeasure ν := by
    constructor
    change (volume.withDensity (fun r => (v r : ℝ≥0∞))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_coe_eq_integral v hw]
    change ENNReal.ofReal (∫ r, w r) = 1
    simp only [hw1, ENNReal.ofReal_one]
  have hgi : Integrable g ν := by
    apply (integrable_withDensity_iff_integrable_smul₀ hv).2
    change Integrable (fun r => w r * g r)
    exact hg
  have hg4i : Integrable (fun r => g r ^ 4) ν := by
    apply (integrable_withDensity_iff_integrable_smul₀ hv).2
    change Integrable (fun r => w r * g r ^ 4)
    simpa only [(show Even (4 : ℕ) by decide).pow_abs] using hg4
  have hj := (show Even (4 : ℕ) by decide).convexOn_pow.map_integral_le
    (continuous_pow 4).continuousOn isClosed_univ (by simp) hgi hg4i
  have hc (f : ℝ → ℝ) : (∫ r, f r ∂ν) = ∫ r, w r * f r :=
    integral_withDensity_eq_integral_smul₀ hv f
  rw [hc, hc] at hj
  simpa only [(show Even (4 : ℕ) by decide).pow_abs] using hj

private theorem sieve_average_fourth (Q : ℕ+) (w : ℝ → ℝ)
    (hw : Integrable w) (hw0 : ∀ r, 0 ≤ w r) (hw1 : (∫ r, w r) = 1)
    (F : ℝ → ZMod (Q : ℕ) → ℝ)
    (hF : ∀ x, Integrable (fun r => w r * F r x))
    (hF4 : ∀ x, Integrable (fun r => w r * |F r x| ^ 4)) :
    sieveExpectation Q (fun x => |∫ r, w r * F r x| ^ 4) ≤
      ∫ r, w r * sieveExpectation Q (fun x => |F r x| ^ 4) := by
  classical
  have hi : (fun r => w r * sieveExpectation Q (fun x => |F r x| ^ 4)) =
      fun r => (∑ x, w r * |F r x| ^ 4) / (Q : ℝ) := by
    funext r
    simp only [sieveExpectation, ← mul_div_assoc, Finset.mul_sum]
  rw [hi, integral_div, integral_finsetSum _ (fun x _ => hF4 x)]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ =>
    weighted_jensen_fourth w (fun r => F r x) hw hw0 hw1 (hF x) (hF4 x))
    (Nat.cast_nonneg _)

private theorem finite_step_integrable (w : ℝ → ℝ) (hw : Integrable w)
    (s : Finset ℕ) (c : ℕ → ℝ) (H a b z : ℝ) (n : ℕ) :
    Integrable (fun r => w r *
      ((∑ d ∈ s, (Ioc (a+r) (b+r)).indicator (fun _ : ℝ => c d) (d / H)) - z) ^ n) := by
  classical
  have hm (d : ℕ) : Measurable (fun r : ℝ =>
      (Ioc (a+r) (b+r)).indicator (fun _ : ℝ => c d) (d / H)) := by
    have hs : MeasurableSet {r : ℝ | (d : ℝ) / H ∈ Ioc (a+r) (b+r)} :=
      (measurableSet_lt (measurable_const.add measurable_id) measurable_const).inter
        (measurableSet_le measurable_const (measurable_const.add measurable_id))
    exact measurable_const.ite hs measurable_const
  have hbound (r : ℝ) :
      |(∑ d ∈ s, (Ioc (a+r) (b+r)).indicator (fun _ : ℝ => c d) (d / H)) - z| ≤
        (∑ d ∈ s, |c d|) + |z| := by
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro d hd
    by_cases h : (d : ℝ) / H ∈ Ioc (a+r) (b+r) <;> simp [h]
  apply hw.mul_bdd
    ((Finset.measurable_sum s (fun d _ => hm d)).sub_const z |>.pow_const n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun r => by
    simpa only [norm_pow, Real.norm_eq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hbound r) n)

private theorem sharp_interval_eq_sum (Q : ℕ+) (H a b : ℝ) (hH : 0 < H)
    (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) (hbN : ⌊b * H⌋₊ ≤ N)
    (x : ZMod (Q : ℕ)) :
    sieveIntervalSum Q H a b x = ∑ d ∈ Finset.Iic N,
      (Ioc a b).indicator (fun _ : ℝ => sieveVariable Q d x) ((d : ℝ) / H) := by
  classical
  have hm (d : ℕ) : d ∈ points H a b ↔ (d : ℝ) / H ∈ Ioc a b := by
    simp only [points, Finset.mem_Ioc, mem_Ioc]
    rw [Nat.floor_lt (mul_nonneg ha hH.le),
      Nat.le_floor_iff (mul_nonneg (ha.trans hab) hH.le),
      lt_div_iff₀ hH, div_le_iff₀ hH]
  have hsub : points H a b ⊆ Finset.Iic N := by
    intro d hd
    exact Finset.mem_Iic.mpr ((Finset.mem_Ioc.mp hd).2.trans hbN)
  change (∑ d ∈ points H a b, sieveVariable Q d x) = _
  calc
    _ = ∑ d ∈ Finset.Iic N, if d ∈ points H a b then sieveVariable Q d x else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset hsub]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [indicator_apply, hm]

private theorem smooth_sum_average (Q : ℕ+) (H δ : ℝ) (hH : 0 < H)
    (hδ : 0 < δ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (x : ZMod (Q : ℕ)) :
    sieveWeightedSum Q H (smoothedInterval δ hδ a b) x =
      ∫ r, smoothingKernel δ hδ r * sieveIntervalSum Q H (a+r) (b+r) x := by
  classical
  let N := ⌊(b + 3 * δ) * H⌋₊
  have hb : 0 ≤ b + 3 * δ := by linarith
  have hs : Function.support (fun d : ℕ => smoothedInterval δ hδ a b ((d : ℝ) / H) * sieveVariable Q d x) ⊆
      ↑(Finset.Iic N) := by
    intro d hd
    have hd' : (d : ℝ) / H ∈ tsupport (smoothedInterval δ hδ a b) :=
      subset_tsupport _ (left_ne_zero_of_mul hd)
    have hdle := ((smooth_interval_support δ hδ a b ha hab).2 hd').2
    exact Finset.mem_Iic.mpr ((Nat.le_floor_iff (mul_nonneg hb hH.le)).mpr
      ((div_le_iff₀ hH).mp hdle))
  have hi (d : ℕ) : Integrable (fun r => smoothingKernel δ hδ r *
      (Ioc (a+r) (b+r)).indicator (fun _ : ℝ => sieveVariable Q d x) ((d : ℝ) / H)) := by
    simpa only [Finset.sum_singleton, sub_zero, pow_one] using
      finite_step_integrable (smoothingKernel δ hδ) (sieveSmoothingBump δ hδ).integrable_normed
        {d} (fun d => sieveVariable Q d x) H a b 0 1
  rw [sieveWeightedSum, finsum_eq_sum_of_support_subset _ hs]
  calc
    _ = ∑ d ∈ Finset.Iic N, ∫ r, smoothingKernel δ hδ r *
        (Ioc (a+r) (b+r)).indicator (fun _ : ℝ => sieveVariable Q d x) ((d : ℝ) / H) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [smoothedInterval, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with r
      by_cases ht : (d : ℝ) / H ∈ Ioc (a+r) (b+r) <;> simp [ht]
    _ = ∫ r, ∑ d ∈ Finset.Iic N, smoothingKernel δ hδ r *
        (Ioc (a+r) (b+r)).indicator (fun _ : ℝ => sieveVariable Q d x) ((d : ℝ) / H) :=
      (integral_finsetSum _ (fun d _ => hi d)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      by_cases hr : smoothingKernel δ hδ r = 0
      · simp [hr]
      have hr' : r ∈ Ioo δ (3 * δ) := by
        rwa [← (smoothing_kernel_support δ hδ).2]
      have har : 0 ≤ a+r := by linarith [hr'.1]
      have habr : a+r ≤ b+r := by linarith
      have hN : ⌊(b+r)*H⌋₊ ≤ N :=
        Nat.floor_mono (mul_le_mul_of_nonneg_right (by linarith [hr'.2]) hH.le)
      rw [sharp_interval_eq_sum Q H (a+r) (b+r) hH har habr N hN x, Finset.mul_sum]

private theorem shift_average_integrable (Q : ℕ+) (H δ : ℝ) (hH : 0 < H)
    (hδ : 0 < δ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (x : ZMod (Q : ℕ)) :
    Integrable (fun r => smoothingKernel δ hδ r *
      (sieveIntervalSum Q H (a+r) (b+r) x - sieveIntervalSum Q H a b x)) ∧
    Integrable (fun r => smoothingKernel δ hδ r *
      |sieveIntervalSum Q H (a+r) (b+r) x - sieveIntervalSum Q H a b x| ^ 4) := by
  let N := ⌊(b + 3 * δ) * H⌋₊
  have hi (n : ℕ) : Integrable (fun r => smoothingKernel δ hδ r *
      (sieveIntervalSum Q H (a+r) (b+r) x - sieveIntervalSum Q H a b x) ^ n) := by
    apply (finite_step_integrable (smoothingKernel δ hδ) (sieveSmoothingBump δ hδ).integrable_normed
      (Finset.Iic N) (fun d => sieveVariable Q d x) H a b (sieveIntervalSum Q H a b x) n).congr
    filter_upwards [] with r
    by_cases hr : smoothingKernel δ hδ r = 0
    · simp [hr]
    have hr' : r ∈ Ioo δ (3 * δ) := by rwa [← (smoothing_kernel_support δ hδ).2]
    have har : 0 ≤ a+r := by linarith [hr'.1]
    have habr : a+r ≤ b+r := by linarith
    have hN : ⌊(b+r)*H⌋₊ ≤ N :=
      Nat.floor_mono (mul_le_mul_of_nonneg_right (by linarith [hr'.2]) hH.le)
    rw [sharp_interval_eq_sum Q H (a+r) (b+r) hH har habr N hN x]
  exact ⟨by simpa only [pow_one] using hi 1,
    by simpa only [(show Even (4 : ℕ) by decide).pow_abs] using hi 4⟩

private theorem sieve_average_norm4_le (Q : ℕ+) (w : ℝ → ℝ)
    (hw : Integrable w) (hw0 : ∀ r, 0 ≤ w r) (hw1 : (∫ r, w r) = 1)
    (F : ℝ → ZMod (Q : ℕ) → ℝ)
    (hF : ∀ x, Integrable (fun r => w r * F r x))
    (hF4 : ∀ x, Integrable (fun r => w r * |F r x| ^ 4))
    (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ r, w r ≠ 0 → sieveNorm4 Q (F r) ≤ D) :
    sieveNorm4 Q (fun x => ∫ r, w r * F r x) ≤ D := by
  classical
  have hi : Integrable (fun r => w r * sieveExpectation Q (fun x => |F r x| ^ 4)) := by
    apply ((integrable_finsetSum Finset.univ (fun x _ => hF4 x)).div_const (Q : ℝ)).congr
    filter_upwards [] with r
    simp only [sieveExpectation, ← mul_div_assoc, Finset.mul_sum]
  apply (pow_le_pow_iff_left₀ (sieve_norm4_nonneg Q _) hD (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [sieve_norm4_fourth]
  calc
    _ ≤ ∫ r, w r * sieveExpectation Q (fun x => |F r x| ^ 4) :=
      sieve_average_fourth Q w hw hw0 hw1 F hF hF4
    _ ≤ ∫ r, w r * D ^ 4 := by
      apply integral_mono hi (hw.mul_const (D ^ 4))
      intro r
      by_cases hr : w r = 0
      · simp [hr]
      apply mul_le_mul_of_nonneg_left _ (hw0 r)
      rw [← sieve_norm4_fourth]
      exact pow_le_pow_left₀ (sieve_norm4_nonneg Q _) (hbound r hr) 4
    _ = D ^ 4 := by rw [integral_mul_const, hw1, one_mul]

private theorem normalized_shift_integrable (Q : ℕ+) (H δ : ℝ) (hH : 0 < H)
    (hδ : 0 < δ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (x : ZMod (Q : ℕ)) :
    Integrable (fun r => smoothingKernel δ hδ r *
      (normalizedIntervalSum Q H a b x - normalizedIntervalSum Q H (a+r) (b+r) x)) ∧
    Integrable (fun r => smoothingKernel δ hδ r *
      |normalizedIntervalSum Q H a b x - normalizedIntervalSum Q H (a+r) (b+r) x| ^ 4) := by
  have hi := shift_average_integrable Q H δ hH hδ a b ha hab x
  constructor
  · apply ((hi.1.div_const (sieveScale H)).neg).congr
    filter_upwards [] with r
    dsimp only [normalizedIntervalSum, Pi.neg_apply]
    ring
  · apply (hi.2.div_const (sieveScale H ^ 4)).congr
    filter_upwards [] with r
    simp only [normalizedIntervalSum, (show Even (4 : ℕ) by decide).pow_abs]
    ring

private theorem normalized_smoothing_average (Q : ℕ+) (H δ : ℝ) (hH : 0 < H)
    (hδ : 0 < δ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (x : ZMod (Q : ℕ)) :
    normalizedIntervalSum Q H a b x - normalizedWeightedSum Q H (smoothedInterval δ hδ a b) x =
      ∫ r, smoothingKernel δ hδ r * (normalizedIntervalSum Q H a b x - normalizedIntervalSum Q H (a+r) (b+r) x) := by
  have hi := (shift_average_integrable Q H δ hH hδ a b ha hab x).1
  have hc : Integrable (fun r => smoothingKernel δ hδ r * sieveIntervalSum Q H a b x) :=
    ((sieveSmoothingBump δ hδ).integrable_normed (μ := volume)).mul_const (sieveIntervalSum Q H a b x)
  have heq : sieveWeightedSum Q H (smoothedInterval δ hδ a b) x =
      (∫ r, smoothingKernel δ hδ r * (sieveIntervalSum Q H (a+r) (b+r) x - sieveIntervalSum Q H a b x)) + sieveIntervalSum Q H a b x := by
    rw [smooth_sum_average Q H δ hH hδ a b ha hab x]
    calc
      _ = ∫ r, (smoothingKernel δ hδ r * (sieveIntervalSum Q H (a+r) (b+r) x - sieveIntervalSum Q H a b x) +
          smoothingKernel δ hδ r * sieveIntervalSum Q H a b x) := by
        apply integral_congr_ae
        filter_upwards [] with r
        ring
      _ = _ := by
        rw [integral_add hi hc, integral_mul_const, (smoothing_kernel_mass δ hδ).2, one_mul]
  calc
    _ = -(∫ r, smoothingKernel δ hδ r * (sieveIntervalSum Q H (a+r) (b+r) x - sieveIntervalSum Q H a b x)) / sieveScale H := by
      dsimp only [normalizedIntervalSum, normalizedWeightedSum]
      rw [heq]
      ring
    _ = _ := by
      rw [← integral_neg, ← integral_div]
      apply integral_congr_ae
      filter_upwards [] with r
      dsimp only [normalizedIntervalSum]
      ring

/-- Positive shift smoothing has a uniform normalized fourth-norm error. -/
theorem sieve_smoothing_norm4_bound (hMS : MSFinite) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ Q : ℕ+, sieveDensity Q ≤ B * Real.log H → ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      sieveNorm4 Q (fun x => normalizedIntervalSum Q H a b x - normalizedWeightedSum Q H (smoothedInterval δ hδ a b) x) ≤
        C * (Real.sqrt δ + H ^ (-1/4 : ℝ)) := by
  obtain ⟨C, hC, hendpoint⟩ := sieve_interval_endpoint_norm4_bound hMS B hB
  have hC0 : 0 ≤ C := by linarith
  refine ⟨2 * C, by linarith, ?_⟩
  filter_upwards [hendpoint, eventually_gt_atTop (0 : ℝ)]
    with H hbound hH Q hP δ hδ _hδ1 a b ha hab
  let F : ℝ → ZMod (Q : ℕ) → ℝ :=
    fun r x => normalizedIntervalSum Q H a b x - normalizedIntervalSum Q H (a+r) (b+r) x
  have hF (x : ZMod (Q : ℕ)) :=
    normalized_shift_integrable Q H δ hH hδ a b ha hab x
  have hD : 0 ≤ C * (Real.sqrt (3 * δ) + H ^ (-1/4 : ℝ)) :=
    mul_nonneg hC0 (add_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hH.le _))
  have hpoint (r : ℝ) (hr : smoothingKernel δ hδ r ≠ 0) :
      sieveNorm4 Q (F r) ≤ C * (Real.sqrt (3 * δ) + H ^ (-1/4 : ℝ)) := by
    have hr' : r ∈ Ioo δ (3 * δ) := by rwa [← (smoothing_kernel_support δ hδ).2]
    have hr0 : 0 ≤ r := by linarith [hr'.1]
    have hdist (u : ℝ) : |u - (u+r)| ≤ 3 * δ := by
      rw [show u - (u+r) = -r by ring, abs_neg, abs_of_nonneg hr0]
      exact hr'.2.le
    exact hbound Q hP a b (a+r) (b+r) (3 * δ) ha hab
      (by linarith) (by linarith) (by positivity) (hdist a) (hdist b)
  calc
    _ = sieveNorm4 Q (fun x => ∫ r, smoothingKernel δ hδ r * F r x) := by
      apply congrArg (sieveNorm4 Q)
      funext x
      exact normalized_smoothing_average Q H δ hH hδ a b ha hab x
    _ ≤ C * (Real.sqrt (3 * δ) + H ^ (-1/4 : ℝ)) :=
      sieve_average_norm4_le Q (smoothingKernel δ hδ) (sieveSmoothingBump δ hδ).integrable_normed
        (smoothing_kernel_mass δ hδ).1 (smoothing_kernel_mass δ hδ).2 F
        (fun x => (hF x).1) (fun x => (hF x).2) _ hD hpoint
    _ ≤ C * (2 * Real.sqrt δ + H ^ (-1/4 : ℝ)) := by
      have hsqrt : Real.sqrt (3 * δ) ≤ 2 * Real.sqrt δ := by
        calc
          _ ≤ Real.sqrt (4 * δ) := Real.sqrt_le_sqrt (by linarith)
          _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
      exact mul_le_mul_of_nonneg_left (add_le_add hsqrt le_rfl) hC0
    _ ≤ (2 * C) * (Real.sqrt δ + H ^ (-1/4 : ℝ)) := by
      have ht : 0 ≤ H ^ (-1/4 : ℝ) := Real.rpow_nonneg hH.le _
      nlinarith [mul_nonneg hC0 ht]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
