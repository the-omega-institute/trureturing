/- GID: D5/S3/Weil/Analytic/NymanLogCorrection
   generality: I
   mirror-B: none(waiver:nyman-signed-prime-support)
   mirror-E: none(waiver:nyman-signed-prime)
   anchors: []
   utility: none
   digest: The logarithmic moment of the fixed shell is a weighted sum of its contractions. -/

import D5.S3.Weil.Analytic.NymanKernelConvolution
import D5.S3.Weil.Analytic.NymanPrimeDilations

/-! The shell's logarithmic moment as a sum of contractions of the original shell. -/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Convolution

namespace NymanLogCorrection

open NymanKernelConvolution (h h_pos q b_exp_eq_fourfold_convolution)
open NymanPrimeDilations (B shell logCorrection logBox logBox_mul_argument)
open NymanFixedRationalKernel (A A_pos b b_zero_right)

private theorem integrable_of_bounded_support {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ} (hs : MeasurableSet s) (hμ : μ s < ⊤)
    (hf : Measurable f) (hz : ∀ x ∉ s, f x = 0) (C : ℝ) (hb : ∀ x ∈ s, ‖f x‖ ≤ C) :
    Integrable f μ := by
  have hI : IntegrableOn f s μ := IntegrableOn.of_bound hμ hf.aestronglyMeasurable C
    ((ae_restrict_iff' hs).2 (Eventually.of_forall hb))
  have hi : s.indicator f = f := by
    funext x
    by_cases hx : x ∈ s
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, hz x hx]
  rw [← hi]
  exact hI.integrable_indicator hs

/-- Pointwise support matters because the convolution identities are evaluated at fixed points. -/
private structure CompactKernel (H : ℝ) (f : ℝ → ℝ) : Prop where
  measurable : Measurable f
  zero : ∀ x ∉ Ioc 0 H, f x = 0
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C

private theorem CompactKernel.integrable {H : ℝ} {f : ℝ → ℝ} (hf : CompactKernel H f) :
    Integrable f := by
  obtain ⟨C, _, hC⟩ := hf.bounded
  exact integrable_of_bounded_support measurableSet_Ioc measure_Ioc_lt_top hf.measurable hf.zero C
    (fun x _ => hC x)

private theorem CompactKernel.slice {H K : ℝ} {f g : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) (t : ℝ) :
    Integrable (fun u => f u * g (t - u)) := by
  obtain ⟨C, hC, hbound⟩ := hg.bounded
  exact (hf.integrable.norm.mul_const C).mono'
    (hf.measurable.mul (hg.measurable.comp (measurable_id.const_sub t))).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))

private theorem CompactKernel.conv {H K : ℝ} {f g : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) : CompactKernel (H + K) (f ⋆ g) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((hf.measurable.comp measurable_snd).mul
      (hg.measurable.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
      |>.integral_prod_right' |>.measurable
  · intro t ht
    change (∫ u : ℝ, f u * g (t - u)) = 0
    rw [← integral_zero (α := ℝ) (G := ℝ) (μ := volume)]
    apply integral_congr_ae
    refine Eventually.of_forall fun u => ?_
    dsimp only
    by_cases hu : u ∈ Ioc 0 H
    · have hv : t - u ∉ Ioc 0 K := by
        intro hv
        exact ht ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩
      rw [hg.zero _ hv, mul_zero]
    · rw [hf.zero _ hu, zero_mul]
  · obtain ⟨C, hC, hbound⟩ := hg.bounded
    refine ⟨∫ u : ℝ, ‖f u‖ * C, ?_, fun t => ?_⟩
    · exact integral_nonneg fun u => mul_nonneg (norm_nonneg _) hC
    · change ‖∫ u : ℝ, f u * g (t - u)‖ ≤ _
      refine (norm_integral_le_integral_norm _).trans
        (integral_mono (hf.slice hg t).norm (hf.integrable.norm.mul_const C) fun u => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)

private def argument (f : ℝ → ℝ) (t : ℝ) : ℝ := t * f t

private theorem CompactKernel.argument {H : ℝ} {f : ℝ → ℝ} (hf : CompactKernel H f) :
    CompactKernel H (argument f) := by
  obtain ⟨C, hC, hbound⟩ := hf.bounded
  refine ⟨measurable_id.mul hf.measurable, ?_, |H| * C, by positivity, ?_⟩
  · intro t ht
    simp [NymanLogCorrection.argument, hf.zero t ht]
  · intro t
    by_cases ht : t ∈ Ioc 0 H
    · rw [NymanLogCorrection.argument, norm_mul, Real.norm_eq_abs, abs_of_pos ht.1]
      exact mul_le_mul (ht.2.trans (le_abs_self H)) (hbound t) (norm_nonneg _) (abs_nonneg _)
    · simp only [NymanLogCorrection.argument, hf.zero t ht, mul_zero, norm_zero]
      positivity

private theorem box_kernel (j : ℕ) : CompactKernel h (q j) := by
  refine ⟨(by fun_prop : Measurable fun u : ℝ => Real.exp ((j : ℝ) * u)).indicator
    measurableSet_Ioc, fun _ ht => indicator_of_notMem ht _, Real.exp ((j : ℝ) * h),
    (Real.exp_pos _).le, ?_⟩
  intro t
  by_cases ht : t ∈ Ioc 0 h
  · rw [q, indicator_of_mem ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_monotone (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg _))
  · rw [q, indicator_of_notMem ht, norm_zero]
    exact (Real.exp_pos _).le

private theorem conv_comm (f g : ℝ → ℝ) : f ⋆ g = g ⋆ f := by
  funext t
  rw [convolution_lsmul_swap (f := f) (g := g), convolution_lsmul (f := g) (g := f)]
  simp only [smul_eq_mul, mul_comm]

private theorem conv_assoc {H K L : ℝ} {f g k : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) (hk : CompactKernel L k) :
    (f ⋆ g) ⋆ k = f ⋆ (g ⋆ k) := by
  funext t
  let m : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  refine convolution_assoc' (μ := volume) (ν := volume) m m m m
    (fun a b c => by change (a * b) * c = a * (b * c); exact mul_assoc a b c)
    (Eventually.of_forall (hf.slice hg)) (Eventually.of_forall (hg.slice hk)) ?_
  obtain ⟨Cf, hCf₀, hCf⟩ := hf.bounded
  obtain ⟨Cg, hCg₀, hCg⟩ := hg.bounded
  obtain ⟨Ck, _, hCk⟩ := hk.bounded
  change Integrable (fun p : ℝ × ℝ => f p.2 * (g (p.1 - p.2) * k (t - p.1)))
    ((volume : Measure ℝ).prod volume)
  refine integrable_of_bounded_support (s := Ioc 0 (H + K) ×ˢ Ioc 0 H)
    (measurableSet_Ioc.prod measurableSet_Ioc)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top)
    ((hf.measurable.comp measurable_snd).mul
      ((hg.measurable.comp (measurable_fst.sub measurable_snd)).mul
        (hk.measurable.comp (measurable_fst.const_sub t)))) ?_ (Cf * (Cg * Ck)) ?_
  · intro p hp
    by_cases hu : p.2 ∈ Ioc 0 H
    · have hv : p.1 - p.2 ∉ Ioc 0 K := by
        intro hv
        exact hp ⟨⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩, hu⟩
      rw [hg.zero _ hv, zero_mul, mul_zero]
    · rw [hf.zero _ hu, zero_mul]
  · intro p _
    simp only [norm_mul]
    exact mul_le_mul (hCf _) (mul_le_mul (hCg _) (hCk _) (norm_nonneg _) hCg₀)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCf₀

private theorem argument_conv {H K : ℝ} {f g : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) :
    argument (f ⋆ g) = (argument f ⋆ g) + (f ⋆ argument g) := by
  funext t
  exact NymanPrimeDilations.logConvolution_mul_argument (hf.argument.slice hg t)
    (hf.slice hg.argument t)

private theorem add_conv {H K L : ℝ} {f g k : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) (hk : CompactKernel L k) :
    (f + g) ⋆ k = (f ⋆ k) + (g ⋆ k) := by
  funext t
  exact ConvolutionExistsAt.add_distrib (hf.slice hk t) (hg.slice hk t)

private def step (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ) * h

private theorem step_eventually_large (r : ℝ) :
    ∃ N : ℕ, ∀ k ∉ Finset.range N, r < step k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (r / h)
  refine ⟨N, fun k hk => ?_⟩
  have hNk : N ≤ k + 1 := by
    have := Nat.le_of_not_gt (fun hlt => hk (Finset.mem_range.mpr hlt))
    omega
  exact ((div_lt_iff₀ h_pos).mp hN).trans_le
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hNk) h_pos.le)

private def weight (j : ℕ) (v : ℝ) : ℝ := Real.exp (-(j : ℝ) * v)

private def positiveWeight (j : ℕ) : ℝ → ℝ := (Ioi 0).indicator (weight j)

private theorem positiveWeight_measurable (j : ℕ) : Measurable (positiveWeight j) :=
  (by unfold weight; fun_prop : Measurable (weight j)).indicator measurableSet_Ioi

private theorem positiveWeight_norm_le (j : ℕ) (v : ℝ) : ‖positiveWeight j v‖ ≤ 1 := by
  by_cases hv : v ∈ Ioi (0 : ℝ)
  · rw [positiveWeight, indicator_of_mem hv, weight, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (mem_Ioi.mp hv).le
  · simp [positiveWeight, indicator_of_notMem hv]

private def shiftSum (j : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, weight j (step k) * f (t + step k)

private def shiftIntegral (j : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ v : ℝ, positiveWeight j v * f (t + v)

private theorem shiftIntegral_eq_setIntegral (j : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    shiftIntegral j f t = ∫ v in Ioi (0 : ℝ), weight j v * f (t + v) := by
  rw [shiftIntegral, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  refine Eventually.of_forall fun v => ?_
  by_cases hv : v ∈ Ioi (0 : ℝ) <;> simp [positiveWeight, hv]

/-- A single finite cutoff works uniformly over the support of the other factor. -/
private theorem shiftSum_conv_right {H K : ℝ} {f g : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) (j : ℕ) (t : ℝ) :
    (∫ u : ℝ, f u * shiftSum j g (t - u)) = shiftSum j (f ⋆ g) t := by
  obtain ⟨N, hN⟩ := step_eventually_large (H + K - t)
  have hzero (u : ℝ) (hu : u ∈ Ioc 0 H) (k : ℕ) (hk : k ∉ Finset.range N) :
      g (t - u + step k) = 0 := by
    apply hg.zero
    intro hv
    linarith [hu.2, hv.2, hN k hk]
  calc
    _ = ∫ u : ℝ, ∑ k ∈ Finset.range N, weight j (step k) * (f u * g (t + step k - u)) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun u => ?_
      dsimp only
      by_cases hu : u ∈ Ioc 0 H
      · rw [shiftSum, tsum_eq_sum (s := Finset.range N)
          (fun k hk => by rw [hzero u hu k hk, mul_zero]), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [show t - u + step k = t + step k - u by ring]
        ring
      · simp [hf.zero u hu]
    _ = ∑ k ∈ Finset.range N, weight j (step k) * (f ⋆ g) (t + step k) := by
      rw [integral_finsetSum _ (fun k _ => (hf.slice hg (t + step k)).const_mul _)]
      simp only [integral_const_mul, convolution_lsmul, smul_eq_mul]
    _ = _ := by
      unfold shiftSum
      rw [tsum_eq_sum (s := Finset.range N)]
      intro k hk
      rw [(hf.conv hg).zero _ (fun hv => by linarith [hv.2, hN k hk]), mul_zero]

/-- For fixed output t the integrand is supported where 0 < u ≤ H and
0 < v ≤ H + K - t, so ordinary Bochner Fubini applies. -/
private theorem integrable_shift_product {H K : ℝ} {f g : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) (j : ℕ) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.1 * (positiveWeight j p.2 * g (t - p.1 + p.2)))
      ((volume : Measure ℝ).prod volume) := by
  obtain ⟨Cf, hCf₀, hCf⟩ := hf.bounded
  obtain ⟨Cg, _, hCg⟩ := hg.bounded
  refine integrable_of_bounded_support (s := Ioc 0 H ×ˢ Ioc 0 (H + K - t))
    (measurableSet_Ioc.prod measurableSet_Ioc)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top)
    ((hf.measurable.comp measurable_fst).mul
      (((positiveWeight_measurable j).comp measurable_snd).mul
        (hg.measurable.comp ((measurable_fst.const_sub t).add measurable_snd)))) ?_ (Cf * Cg) ?_
  · intro p hp
    by_cases hu : p.1 ∈ Ioc 0 H
    · by_cases hv : p.2 ∈ Ioi (0 : ℝ)
      · have hv' : H + K - t < p.2 :=
          lt_of_not_ge fun hv' => hp ⟨hu, ⟨hv, hv'⟩⟩
        rw [hg.zero _ (fun hs => by linarith [hs.2, hu.2]), mul_zero, mul_zero]
      · rw [positiveWeight, indicator_of_notMem hv, zero_mul, mul_zero]
    · rw [hf.zero _ hu, zero_mul]
  · intro p _
    simp only [norm_mul]
    refine mul_le_mul (hCf _) ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCf₀
    simpa only [one_mul] using
      mul_le_mul (positiveWeight_norm_le j p.2) (hCg _) (norm_nonneg _) zero_le_one

private theorem shiftIntegral_conv_right {H K : ℝ} {f g : ℝ → ℝ}
    (hf : CompactKernel H f) (hg : CompactKernel K g) (j : ℕ) (t : ℝ) :
    (∫ u : ℝ, f u * shiftIntegral j g (t - u)) = shiftIntegral j (f ⋆ g) t := by
  simp only [shiftIntegral, ← integral_const_mul]
  rw [integral_integral_swap (integrable_shift_product hf hg j t)]
  apply integral_congr_ae
  refine Eventually.of_forall fun v => ?_
  simp only [convolution_lsmul, smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun u => ?_
  dsimp only
  rw [show t - u + v = t + v - u by ring, mul_left_comm]

private theorem conv_argument_box {H : ℝ} {f : ℝ → ℝ}
    (hf : CompactKernel H f) (j : ℕ) (t : ℝ) :
    (f ⋆ argument (q j)) t =
      h * (f ⋆ q j) t + h * shiftSum j (f ⋆ q j) t - shiftIntegral j (f ⋆ q j) t := by
  have hbox (u : ℝ) : argument (q j) u =
      h * q j u + h * shiftSum j (q j) u - shiftIntegral j (q j) u := by
    rw [shiftIntegral_eq_setIntegral]
    exact logBox_mul_argument h_pos (j : ℝ) u
  have hI : Integrable (fun u => f u * shiftIntegral j (q j) (t - u)) := by
    simpa only [shiftIntegral, ← integral_const_mul] using
      (integrable_shift_product hf (box_kernel j) j t).integral_prod_left
  have hS : Integrable (fun u => f u * shiftSum j (q j) (t - u)) := by
    obtain ⟨N, hN⟩ := step_eventually_large (H + h - t)
    have hfinite (u : ℝ) :
        f u * shiftSum j (q j) (t - u) =
          ∑ k ∈ Finset.range N, weight j (step k) * (f u * q j (t + step k - u)) := by
      by_cases hu : u ∈ Ioc 0 H
      · rw [shiftSum, tsum_eq_sum (s := Finset.range N), Finset.mul_sum]
        · apply Finset.sum_congr rfl
          intro k _
          rw [show t - u + step k = t + step k - u by ring]
          ring
        · intro k hk
          rw [(box_kernel j).zero _ (fun hv => by linarith [hu.2, hv.2, hN k hk]), mul_zero]
      · simp [hf.zero u hu]
    simp_rw [hfinite]
    exact integrable_finsetSum _ (fun k _ => (hf.slice (box_kernel j) (t + step k)).const_mul _)
  calc
    _ = ∫ u : ℝ, h * (f u * q j (t - u)) + h * (f u * shiftSum j (q j) (t - u)) -
          f u * shiftIntegral j (q j) (t - u) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        change f u * argument (q j) (t - u) = _
        rw [hbox]
        ring
    _ = _ := by
      have hq := (hf.slice (box_kernel j) t).const_mul h
      have hS' := hS.const_mul h
      have hAdd : Integrable
          (fun u => h * (f u * q j (t - u)) + h * (f u * shiftSum j (q j) (t - u))) :=
        hq.add hS'
      rw [integral_sub hAdd hI, integral_add hq hS', integral_const_mul, integral_const_mul,
        shiftSum_conv_right hf (box_kernel j), shiftIntegral_conv_right hf (box_kernel j)]
      rfl

private def kernel (t : ℝ) : ℝ := b (Real.exp t)

private theorem kernel_eq_convolution : kernel = ((q 0 ⋆ q 1) ⋆ q 2) ⋆ q 3 :=
  funext b_exp_eq_fourfold_convolution

private theorem kernel_compact : CompactKernel (h + h + h + h) kernel := by
  rw [kernel_eq_convolution]
  exact (((box_kernel 0).conv (box_kernel 1)).conv (box_kernel 2)).conv (box_kernel 3)

private theorem kernel_log_formula (t : ℝ) :
    t * kernel t = 4 * h * kernel t +
      ∑ j : Fin 4, (h * shiftSum j.val kernel t - shiftIntegral j.val kernel t) := by
  let Q := ((q 0 ⋆ q 1) ⋆ q 2) ⋆ q 3
  let L (j : ℕ) := h * Q t + h * shiftSum j Q t - shiftIntegral j Q t
  have h0 := box_kernel 0
  have h1 := box_kernel 1
  have h2 := box_kernel 2
  have h3 := box_kernel 3
  have expand012 : argument ((q 0 ⋆ q 1) ⋆ q 2) =
      ((argument (q 0) ⋆ q 1) ⋆ q 2) + ((q 0 ⋆ argument (q 1)) ⋆ q 2) +
        ((q 0 ⋆ q 1) ⋆ argument (q 2)) := by
    rw [argument_conv (h0.conv h1) h2, argument_conv h0 h1,
      add_conv (h0.argument.conv h1) (h0.conv h1.argument) h2]
  have expand : argument Q =
      (((argument (q 0) ⋆ q 1) ⋆ q 2) ⋆ q 3) +
      (((q 0 ⋆ argument (q 1)) ⋆ q 2) ⋆ q 3) +
      (((q 0 ⋆ q 1) ⋆ argument (q 2)) ⋆ q 3) +
      (((q 0 ⋆ q 1) ⋆ q 2) ⋆ argument (q 3)) := by
    unfold Q
    rw [argument_conv ((h0.conv h1).conv h2) h3, expand012,
      add_conv
        (show CompactKernel (h + h + h) (((argument (q 0) ⋆ q 1) ⋆ q 2) +
            ((q 0 ⋆ argument (q 1)) ⋆ q 2)) from by
          exact ⟨((h0.argument.conv h1).conv h2).measurable.add
                    ((h0.conv h1.argument).conv h2).measurable,
            fun u hu => by
              simp [Pi.add_apply, ((h0.argument.conv h1).conv h2).zero u hu,
                ((h0.conv h1.argument).conv h2).zero u hu],
            by
              obtain ⟨C, hC, hf⟩ := ((h0.argument.conv h1).conv h2).bounded
              obtain ⟨D, hD, hg⟩ := ((h0.conv h1.argument).conv h2).bounded
              exact ⟨C + D, add_nonneg hC hD, fun u =>
                (norm_add_le _ _).trans (add_le_add (hf u) (hg u))⟩⟩)
        ((h0.conv h1).conv h2.argument) h3,
      add_conv ((h0.argument.conv h1).conv h2) ((h0.conv h1.argument).conv h2) h3]
  have move0 {g : ℝ → ℝ} (hg : CompactKernel h g) :
      ((g ⋆ q 1) ⋆ q 2) ⋆ q 3 = ((q 1 ⋆ q 2) ⋆ q 3) ⋆ g := by
    rw [conv_assoc hg h1 h2, conv_assoc hg (h1.conv h2) h3,
      conv_comm g ((q 1 ⋆ q 2) ⋆ q 3)]
  have move1 {g : ℝ → ℝ} (hg : CompactKernel h g) :
      ((q 0 ⋆ g) ⋆ q 2) ⋆ q 3 = ((q 0 ⋆ q 2) ⋆ q 3) ⋆ g := by
    rw [conv_comm (q 0) g, conv_assoc hg h0 h2, conv_assoc hg (h0.conv h2) h3,
      conv_comm g ((q 0 ⋆ q 2) ⋆ q 3)]
  have move2 {g : ℝ → ℝ} (hg : CompactKernel h g) :
      ((q 0 ⋆ q 1) ⋆ g) ⋆ q 3 = ((q 0 ⋆ q 1) ⋆ q 3) ⋆ g := by
    rw [conv_assoc (h0.conv h1) hg h3, conv_comm g (q 3),
      ← conv_assoc (h0.conv h1) h3 hg]
  have term0 : ((((q 1 ⋆ q 2) ⋆ q 3) ⋆ argument (q 0)) t) = L 0 := by
    simpa only [L, Q, ← move0 h0] using conv_argument_box ((h1.conv h2).conv h3) 0 t
  have term1 : ((((q 0 ⋆ q 2) ⋆ q 3) ⋆ argument (q 1)) t) = L 1 := by
    simpa only [L, Q, ← move1 h1] using conv_argument_box ((h0.conv h2).conv h3) 1 t
  have term2 : ((((q 0 ⋆ q 1) ⋆ q 3) ⋆ argument (q 2)) t) = L 2 := by
    simpa only [L, Q, ← move2 h2] using conv_argument_box ((h0.conv h1).conv h3) 2 t
  have term3 : ((((q 0 ⋆ q 1) ⋆ q 2) ⋆ argument (q 3)) t) = L 3 :=
    conv_argument_box ((h0.conv h1).conv h2) 3 t
  rw [kernel_eq_convolution]
  change argument Q t = _
  rw [expand, move0 h0.argument, move1 h1.argument, move2 h2.argument]
  simp only [Pi.add_apply, term0, term1, term2, term3, L]
  norm_num [Fin.sum_univ_succ, Q]
  ring

open scoped ArithmeticFunction.Moebius

private def cutoff (x : ℝ) : Finset ℕ := Finset.Ioc 0 ⌊B * x⌋₊

private theorem dilated_argument {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (v : ℝ) :
    Real.exp (Real.log ((n : ℝ) / x) + v) = (n : ℝ) / (x * Real.exp (-v)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.exp_add, Real.exp_log (div_pos hn' hx), Real.exp_neg, div_mul_eq_div_div,
    div_inv_eq_mul]

/-- Pad the contracted shell to the original cutoff using the right endpoint of b. -/
private theorem shell_dilate_eq_sum {x v : ℝ} (hx : 0 < x) (hv : 0 ≤ v) :
    shell (x * Real.exp (-v)) =
      ∑ n ∈ cutoff x, (μ n : ℝ) * kernel (Real.log ((n : ℝ) / x) + v) := by
  let y := x * Real.exp (-v)
  have hy : 0 < y := mul_pos hx (Real.exp_pos _)
  have hyx : y ≤ x := by
    change x * Real.exp (-v) ≤ x
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)) hx.le
  have hs : cutoff y ⊆ cutoff x := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn0, hnN.trans
      (Nat.floor_mono (mul_le_mul_of_nonneg_left hyx (pow_nonneg A_pos.le _)))⟩
  change (∑ n ∈ cutoff y, (μ n : ℝ) * b ((n : ℝ) / y)) = _
  have harg (n : ℕ) (hn : n ∈ cutoff x) :
      kernel (Real.log ((n : ℝ) / x) + v) = b ((n : ℝ) / y) := by
    unfold kernel
    rw [dilated_argument hx (Finset.mem_Ioc.mp hn).1]
  calc
    _ = ∑ n ∈ cutoff x, (μ n : ℝ) * b ((n : ℝ) / y) := by
      apply Finset.sum_subset hs
      intro n hn hny
      have hlt : ⌊B * y⌋₊ < n :=
        lt_of_not_ge fun hle => hny (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, hle⟩)
      rw [b_zero_right ((le_div_iff₀ hy).mpr (Nat.lt_of_floor_lt hlt).le), mul_zero]
    _ = _ := Finset.sum_congr rfl fun n hn => congrArg ((μ n : ℝ) * ·) (harg n hn).symm

private theorem step_pos (k : ℕ) : 0 < step k := by
  unfold step
  exact mul_pos (by exact_mod_cast Nat.succ_pos k) h_pos

private theorem dilated_tsum_eq {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (∑ n ∈ cutoff x, (μ n : ℝ) * shiftSum j kernel (Real.log ((n : ℝ) / x))) =
      ∑' k : ℕ, weight j (step k) * shell (x * Real.exp (-step k)) := by
  let F (n k : ℕ) := (μ n : ℝ) *
    (weight j (step k) * kernel (Real.log ((n : ℝ) / x) + step k))
  have hF (n : ℕ) : Summable (F n) := by
    obtain ⟨N, hN⟩ :=
      step_eventually_large (h + h + h + h - Real.log ((n : ℝ) / x))
    refine summable_of_ne_finset_zero (s := Finset.range N) (fun k hk => ?_)
    have hz : kernel (Real.log ((n : ℝ) / x) + step k) = 0 :=
      kernel_compact.zero _ (fun hv => by linarith [hv.2, hN k hk])
    simp only [F, hz, mul_zero]
  calc
    _ = ∑ n ∈ cutoff x, ∑' k : ℕ, F n k := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [F, shiftSum, tsum_mul_left]
    _ = ∑' k : ℕ, ∑ n ∈ cutoff x, F n k :=
      (Summable.tsum_finsetSum (fun n _ => hF n)).symm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [shell_dilate_eq_sum hx (step_pos k).le, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      unfold F
      ring

private theorem integrable_kernel_shift (j : ℕ) (t : ℝ) :
    IntegrableOn (fun v => weight j v * kernel (t + v)) (Ioi 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi]
  have hind : (Ioi (0 : ℝ)).indicator (fun v => weight j v * kernel (t + v)) =
      fun v => positiveWeight j v * kernel (t + v) := by
    funext v
    by_cases hv : v ∈ Ioi (0 : ℝ) <;> simp [positiveWeight, hv]
  rw [hind]
  obtain ⟨C, _, hC⟩ := kernel_compact.bounded
  refine integrable_of_bounded_support (s := Ioc 0 (h + h + h + h - t))
    measurableSet_Ioc measure_Ioc_lt_top
    ((positiveWeight_measurable j).mul (kernel_compact.measurable.comp
      (measurable_id.const_add t))) ?_ C ?_
  · intro v hv
    by_cases hv₀ : 0 < v
    · have hv₁ : h + h + h + h - t < v := lt_of_not_ge (fun hle => hv ⟨hv₀, hle⟩)
      rw [kernel_compact.zero _ (fun hu => by linarith [hv₁, hu.2]), mul_zero]
    · rw [positiveWeight, indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv₀), zero_mul]
  · intro v _
    rw [norm_mul]
    exact (mul_le_mul (positiveWeight_norm_le j v) (hC _) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul C)

private theorem dilated_integral_eq {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (∑ n ∈ cutoff x, (μ n : ℝ) * shiftIntegral j kernel (Real.log ((n : ℝ) / x))) =
      ∫ v in Ioi (0 : ℝ), weight j v * shell (x * Real.exp (-v)) := by
  calc
    _ = ∑ n ∈ cutoff x, ∫ v in Ioi (0 : ℝ), (μ n : ℝ) *
        (weight j v * kernel (Real.log ((n : ℝ) / x) + v)) := by
      simp only [shiftIntegral_eq_setIntegral, integral_const_mul]
    _ = ∫ v in Ioi (0 : ℝ), ∑ n ∈ cutoff x, (μ n : ℝ) *
        (weight j v * kernel (Real.log ((n : ℝ) / x) + v)) := by
      symm
      exact integral_finsetSum _ fun n _ =>
        (integrable_kernel_shift j (Real.log ((n : ℝ) / x))).const_mul _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [shell_dilate_eq_sum hx (mem_Ioi.mp hv).le, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring

/-- The logarithmic correction is a sum of weighted contractions of the Möbius shell. -/
theorem logCorrection_eq_dilations {x : ℝ} (hx : 0 < x) :
    logCorrection x = 4 * h * shell x +
      ∑ j : Fin 4,
        (h * (∑' k : ℕ, Real.exp (-(j.val : ℝ) * (((k + 1 : ℕ) : ℝ) * h)) *
            shell (x * Real.exp (-(((k + 1 : ℕ) : ℝ) * h)))) -
          ∫ v in Ioi (0 : ℝ), Real.exp (-(j.val : ℝ) * v) *
            shell (x * Real.exp (-v))) := by
  change logCorrection x = 4 * h * shell x +
    ∑ j : Fin 4, (h * (∑' k : ℕ, weight j.val (step k) * shell (x * Real.exp (-step k))) -
      ∫ v in Ioi (0 : ℝ), weight j.val v * shell (x * Real.exp (-v)))
  simp_rw [← dilated_tsum_eq hx, ← dilated_integral_eq hx]
  have hS : shell x = ∑ n ∈ cutoff x, (μ n : ℝ) * kernel (Real.log ((n : ℝ) / x)) := by
    simpa only [neg_zero, Real.exp_zero, mul_one, add_zero] using
      shell_dilate_eq_sum hx (v := 0) le_rfl
  rw [hS]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := cutoff x), ← Finset.sum_add_distrib]
  unfold logCorrection
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hb : b ((n : ℝ) / x) = kernel (Real.log ((n : ℝ) / x)) := by
    rw [kernel, Real.exp_log (div_pos hn' hx)]
  rw [hb]
  have hlog := congrArg ((μ n : ℝ) * ·) (kernel_log_formula (Real.log ((n : ℝ) / x)))
  simp_rw [mul_add, Finset.mul_sum, mul_sub] at hlog
  convert hlog using 1 <;> norm_num [Fin.sum_univ_succ] <;> ring

end NymanLogCorrection
