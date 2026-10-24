/- GID: D5/S3/Arith/Robin/ForwardKernelFiniteMellin
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernelFiniteMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite positive-center Mellin corrections are entire. -/

import D5.S3.Arith.Robin.ForwardKernelAdjoint
import D5.S3.Arith.Robin.ForwardKernelAnalytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace D5.S3.Arith.Robin.ForwardKernelFiniteMellin

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

local macro "rowSupplier%" name:ident : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.D5.S3.Arith.Robin.OriginalMovingCutRow 0).append
    `D5.S3.Arith.Robin.OriginalMovingCutRow).append name.getId))

/-- An integrable density on a compact interval of positive real centers has an
entire Mellin transform, without any continuity assumption on that density. -/
theorem compact_mellin_entire {a b : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) :
    Differentiable ℂ (fun s : ℂ =>
      ∫ x in Icc a b, f x * (x : ℂ) ^ (-s - 1)) := by
  intro s
  let μ := volume.restrict (Icc a b)
  let dp : ℂ × ℝ → ℂ := fun p =>
    -(Complex.log (p.2 : ℂ)) * (p.2 : ℂ) ^ (-p.1 - 1)
  have hdp : ContinuousOn dp (Metric.closedBall s 1 ×ˢ Icc a b) := by
    apply ContinuousOn.mul
    · exact ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.clog
        (fun p hp => Complex.ofReal_mem_slitPlane.mpr (ha.trans_le hp.2.1))).neg
    · apply ContinuousOn.cpow
      · exact (Complex.continuous_ofReal.comp continuous_snd).continuousOn
      · fun_prop
      · intro p hp
        exact Complex.ofReal_mem_slitPlane.mpr (ha.trans_le hp.2.1)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall s 1).prod isCompact_Icc).bddAbove_image
    hdp.norm
  have hbound (z : ℂ) (hz : z ∈ Metric.ball s 1) (x : ℝ) (hx : x ∈ Icc a b) :
      ‖dp (z, x)‖ ≤ max 0 M :=
    (hM (mem_image_of_mem _ ⟨Metric.ball_subset_closedBall hz, hx⟩)).trans
      (le_max_right _ _)
  have hd (z : ℂ) (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y : ℂ => f x * (x : ℂ) ^ (-y - 1))
        (f x * dp (z, x)) z := by
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hx.1).ne'
    have hp := ((hasDerivAt_id z).neg.sub_const (1 : ℂ)).const_cpow (Or.inl hx0)
    convert hp.const_mul (f x) using 1 <;> dsimp [dp] <;> ring
  have hpmeas (z : ℂ) : Measurable (fun x : ℝ => (x : ℂ) ^ (-z - 1)) :=
    Complex.measurable_ofReal.pow_const _
  have hdmeas (z : ℂ) : Measurable (fun x : ℝ => dp (z, x)) := by
    exact ((Complex.measurable_log.comp Complex.measurable_ofReal).neg).mul (hpmeas z)
  have hbase : Integrable (fun x : ℝ => f x * (x : ℂ) ^ (-s - 1)) μ := by
    apply hf.mul_continuousOn _ isCompact_Icc
    apply Complex.continuous_ofReal.continuousOn.cpow_const
    intro x hx
    exact Complex.ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)
  have hmeas : ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (fun x : ℝ => f x * (x : ℂ) ^ (-z - 1)) μ :=
    Eventually.of_forall fun z => hf.aestronglyMeasurable.mul (hpmeas z).aestronglyMeasurable
  have hderivmeas : AEStronglyMeasurable (fun x : ℝ => f x * dp (s, x)) μ :=
    hf.aestronglyMeasurable.mul (hdmeas s).aestronglyMeasurable
  have hboundint : Integrable (fun x : ℝ => ‖f x‖ * max 0 M) μ :=
    hf.norm.mul_const _
  have hb : ∀ᵐ x : ℝ ∂μ, ∀ z ∈ Metric.ball s 1,
      ‖f x * dp (z, x)‖ ≤ ‖f x‖ * max 0 M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound z hz x hx) (norm_nonneg _)
  have hdiff : ∀ᵐ x : ℝ ∂μ, ∀ z ∈ Metric.ball s 1,
      HasDerivAt (fun y : ℂ => f x * (x : ℂ) ^ (-y - 1))
        (f x * dp (z, x)) z := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx z _hz
    exact hd z x hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s (by norm_num : (0 : ℝ) < 1)) hmeas hbase
    hderivmeas hb hboundint hdiff).2.differentiableAt

/-- Every fixed evaluation point of the original adjoint has entire dependence
on the Mellin parameter. -/
theorem adjointKernel_entire {x0 : ℝ} (hx0 : 4 ≤ x0) (t : ℝ) :
    Differentiable ℂ (fun s => ForwardKernelAdjoint.adjointKernel x0 s t) := by
  have hi : IntegrableOn (fun x : ℝ => (OriginalMovingWindowMoment.kernel x t : ℂ))
      (Icc x0 (max x0 t)) := by
    have h := ForwardKernelAdjoint.adjointKernel_center_integrable hx0 (-1 : ℂ) t
    simp only [neg_neg, sub_self, Complex.cpow_zero, one_mul] at h
    exact h.mono_set Icc_subset_Ici_self
  have he (s : ℂ) : ForwardKernelAdjoint.adjointKernel x0 s t =
      ∫ x in Icc x0 (max x0 t),
        (OriginalMovingWindowMoment.kernel x t : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [ForwardKernelAdjoint.adjointKernel_eq_compact]
    unfold ForwardKernelAdjoint.compactAdjoint
    simp_rw [mul_comm]
  simp_rw [he]
  exact compact_mellin_entire (by linarith) hi

private lemma adjointKernel_measurable (x0 : ℝ) (s : ℂ) :
    Measurable (fun t => ForwardKernelAdjoint.adjointKernel x0 s t) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (p.2 : ℂ) ^ (-s - 1) * (OriginalMovingWindowMoment.kernel p.2 p.1 : ℂ)) :=
    ((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul
      (Complex.measurable_ofReal.comp
        (OriginalMovingCutAggregate.measurable_kernel_joint.comp measurable_swap))
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ici x0))).measurable

private lemma adjointKernel_eq_fixed {x0 b t : ℝ} (hxb : x0 ≤ b) (htb : t ≤ b) (s : ℂ) :
    ForwardKernelAdjoint.adjointKernel x0 s t =
      ∫ x in Icc x0 b, (x : ℂ) ^ (-s - 1) *
        (OriginalMovingWindowMoment.kernel x t : ℂ) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Icc_subset_Ici_self
  intro x hx
  have hbx : b < x := lt_of_not_ge (fun h => hx.2 ⟨hx.1, h⟩)
  simp [OriginalMovingWindowMoment.kernel, not_lt.mpr (htb.trans hbx.le)]

/-- The contribution of every fixed bounded interval of the adjoint is entire. -/
theorem adjointKernel_finite_integral_entire {x0 b : ℝ} (hx0 : 4 ≤ x0) (hxb : x0 ≤ b) :
    Differentiable ℂ (fun s =>
      ∫ t in Icc (1 : ℝ) b, ForwardKernelAdjoint.adjointKernel x0 s t) := by
  apply ForwardKernelAnalytic.entire_integral_of_compact_bound
    (fun s => (adjointKernel_measurable x0 s).aestronglyMeasurable)
    (Eventually.of_forall (adjointKernel_entire hx0))
  intro K hK
  have hc : ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ) ^ (-p.1 - 1)) (K ×ˢ Icc x0 b) := by
    apply ContinuousOn.cpow
    · exact (Complex.continuous_ofReal.comp continuous_snd).continuousOn
    · fun_prop
    · intro p hp
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [hp.2.1])
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).bddAbove_image hc.norm
  refine ⟨max 0 M * volume.real (Icc x0 b), ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht s hs
  rw [adjointKernel_eq_fixed hxb ht.2]
  apply norm_setIntegral_le_of_norm_le_const (by simp)
  intro x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((rowSupplier% kernel_nonneg) (hx0.trans hx.1))]
  have hpower : ‖(x : ℂ) ^ (-s - 1)‖ ≤ max 0 M :=
    (hM (mem_image_of_mem _ (show (s, x) ∈ K ×ˢ Icc x0 b from ⟨hs, hx⟩))).trans
      (le_max_right _ _)
  exact (mul_le_mul_of_nonneg_left
    ((rowSupplier% kernel_le_one) (hx0.trans hx.1)) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hpower)

/-- The bounded signed correction after subtracting the triangular principal kernel. -/
def finiteCorrection (x0 b : ℝ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
    (ForwardKernelAdjoint.adjointKernel x0 s n -
      (1 / 2 : ℂ) * (n : ℂ) ^ (-s - 1 / 2))) -
    ((∫ t in Icc (1 : ℝ) b, ForwardKernelAdjoint.adjointKernel x0 s t) -
      ∫ t in Icc (1 : ℝ) b, (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2))

/-- Both the finite prime-power sum and its Lebesgue-density correction are entire. -/
theorem finiteCorrection_entire {x0 b : ℝ} (hx0 : 4 ≤ x0) (hxb : x0 ≤ b) :
    Differentiable ℂ (finiteCorrection x0 b) := by
  have hsum : Differentiable ℂ (fun s : ℂ =>
      ∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (ForwardKernelAdjoint.adjointKernel x0 s n -
          (1 / 2 : ℂ) * (n : ℂ) ^ (-s - 1 / 2))) := by
    apply Differentiable.fun_sum
    intro n _hn
    by_cases hn : n = 0
    · subst n
      simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul]
      exact differentiable_const _
    · exact ((adjointKernel_entire hx0 n).sub
        (((differentiable_id.neg.sub_const (1 / 2 : ℂ)).const_cpow
          (Or.inl (Nat.cast_ne_zero.mpr hn))).const_mul (1 / 2 : ℂ))).const_mul _
  have hp := (compact_mellin_entire (b := b) zero_lt_one
    (integrableOn_const (C := (1 / 2 : ℂ)) (by simp : volume (Icc (1 : ℝ) b) ≠ ⊤))).comp
      (differentiable_id.sub_const (1 / 2 : ℂ))
  have hp' : Differentiable ℂ (fun s : ℂ =>
      ∫ t in Icc (1 : ℝ) b, (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2)) := by
    convert hp using 1
    funext s
    apply setIntegral_congr_fun measurableSet_Icc
    intro t _
    dsimp only [Function.comp_def, id_eq]
    congr 2
    ring
  exact hsum.sub ((adjointKernel_finite_integral_entire hx0 hxb).sub hp')

#print axioms compact_mellin_entire
#print axioms adjointKernel_entire
#print axioms adjointKernel_finite_integral_entire
#print axioms finiteCorrection_entire

end
end D5.S3.Arith.Robin.ForwardKernelFiniteMellin
