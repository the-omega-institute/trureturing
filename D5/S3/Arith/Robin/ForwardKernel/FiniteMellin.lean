/- GID: D5/S3/Arith/Robin/ForwardKernel/FiniteMellin
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FiniteMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite positive-center Mellin corrections are entire. -/

import D5.S3.Arith.Robin.ForwardKernel.Adjoint
import D5.S3.Arith.Robin.ForwardKernel.Analytic
import Mathlib.Analysis.MellinTransform

namespace D5.S3.Arith.Robin.ForwardKernel.FiniteMellin

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- An integrable density on a compact interval of positive real centers has an
entire Mellin transform, without any continuity assumption on that density. -/
theorem compact_mellin_entire {a b : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) :
    Differentiable ℂ (fun s : ℂ =>
      ∫ x in Icc a b, f x * (x : ℂ) ^ (-s - 1)) := by
  let g : ℝ → ℂ := (Icc a b).indicator f
  have hg : LocallyIntegrableOn g (Ioi 0) :=
    (hf.integrable_indicator measurableSet_Icc).locallyIntegrable.locallyIntegrableOn _
  have htop : g =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop b] with x hx
    exact indicator_of_notMem (fun h : x ∈ Icc a b => hx.not_ge h.2) f
  have hbot : g =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [(eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with x hx
    exact indicator_of_notMem (fun h : x ∈ Icc a b => hx.not_ge h.1) f
  have hm : Differentiable ℂ (mellin g) := by
    intro z
    exact mellin_differentiableAt_of_isBigO_rpow
      (a := z.re + 1) (b := z.re - 1) hg
      (htop.isBigO.trans (Asymptotics.isBigO_zero _ _)) (by linarith)
      (hbot.isBigO.trans (Asymptotics.isBigO_zero _ _)) (by linarith)
  have he (s : ℂ) : mellin g (-s) =
      ∫ x in Icc a b, f x * (x : ℂ) ^ (-s - 1) := by
    change (∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (-s - 1) * (Icc a b).indicator f x) = _
    have hi : (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (Icc a b).indicator f x) =
        (Icc a b).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1) * f x) := by
      funext x
      exact (indicator_mul_right (Icc a b) (fun x : ℝ => (x : ℂ) ^ (-s - 1)) f
        (i := x)).symm
    rw [hi, integral_indicator measurableSet_Icc,
      Measure.restrict_restrict_of_subset
        (show Icc a b ⊆ Ioi 0 from fun x hx => ha.trans_le hx.1)]
    simp only [mul_comm]
  simpa only [Function.comp_def, Pi.neg_apply, id_eq, he] using hm.comp differentiable_id.neg

/-- Every fixed evaluation point of the original adjoint has entire dependence
on the Mellin parameter. -/
theorem adjointKernel_entire {x0 : ℝ} (hx0 : 4 ≤ x0) (t : ℝ) :
    Differentiable ℂ (fun s => ForwardKernel.Adjoint.adjointKernel x0 s t) := by
  have hi : IntegrableOn (fun x : ℝ => (OriginalMovingWindowMoment.kernel x t : ℂ))
      (Icc x0 (max x0 t)) := by
    have h := ForwardKernel.Adjoint.adjointKernel_center_integrable hx0 (-1 : ℂ) t
    simp only [neg_neg, sub_self, Complex.cpow_zero, one_mul] at h
    exact h.mono_set Icc_subset_Ici_self
  have he (s : ℂ) : ForwardKernel.Adjoint.adjointKernel x0 s t =
      ∫ x in Icc x0 (max x0 t),
        (OriginalMovingWindowMoment.kernel x t : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [ForwardKernel.Adjoint.adjointKernel_eq_compact]
    unfold ForwardKernel.Adjoint.compactAdjoint
    simp_rw [mul_comm]
  simp_rw [he]
  exact compact_mellin_entire (by linarith) hi

private lemma adjointKernel_measurable (x0 : ℝ) (s : ℂ) :
    Measurable (fun t => ForwardKernel.Adjoint.adjointKernel x0 s t) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (p.2 : ℂ) ^ (-s - 1) * (OriginalMovingWindowMoment.kernel p.2 p.1 : ℂ)) :=
    ((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul
      (Complex.measurable_ofReal.comp
        (OriginalMovingCutAggregate.measurable_kernel_joint.comp measurable_swap))
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ici x0))).measurable

private lemma adjointKernel_eq_fixed {x0 b t : ℝ} (hxb : x0 ≤ b) (htb : t ≤ b) (s : ℂ) :
    ForwardKernel.Adjoint.adjointKernel x0 s t =
      ∫ x in Icc x0 b, (x : ℂ) ^ (-s - 1) *
        (OriginalMovingWindowMoment.kernel x t : ℂ) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Icc_subset_Ici_self
  intro x hx
  have hbx : b < x := lt_of_not_ge (fun h => hx.2 ⟨hx.1, h⟩)
  simp [OriginalMovingWindowMoment.kernel, not_lt.mpr (htb.trans hbx.le)]

/-- The contribution of every fixed bounded interval of the adjoint is entire. -/
theorem adjointKernel_finite_integral_entire {x0 b : ℝ} (hx0 : 4 ≤ x0) (hxb : x0 ≤ b) :
    Differentiable ℂ (fun s =>
      ∫ t in Icc (1 : ℝ) b, ForwardKernel.Adjoint.adjointKernel x0 s t) := by
  apply ForwardKernel.Analytic.entire_integral_of_compact_bound
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
    abs_of_nonneg (OriginalMovingCutRow.kernel_nonneg (hx0.trans hx.1))]
  have hpower : ‖(x : ℂ) ^ (-s - 1)‖ ≤ max 0 M :=
    (hM (mem_image_of_mem _ (show (s, x) ∈ K ×ˢ Icc x0 b from ⟨hs, hx⟩))).trans
      (le_max_right _ _)
  exact (mul_le_mul_of_nonneg_left
    (OriginalMovingCutRow.kernel_le_one (hx0.trans hx.1)) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hpower)

/-- The bounded signed correction after subtracting the triangular principal kernel. -/
def finiteCorrection (x0 b : ℝ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
    (ForwardKernel.Adjoint.adjointKernel x0 s n -
      (1 / 2 : ℂ) * (n : ℂ) ^ (-s - 1 / 2))) -
    ((∫ t in Icc (1 : ℝ) b, ForwardKernel.Adjoint.adjointKernel x0 s t) -
      ∫ t in Icc (1 : ℝ) b, (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2))

/-- Both the finite prime-power sum and its Lebesgue-density correction are entire. -/
theorem finiteCorrection_entire {x0 b : ℝ} (hx0 : 4 ≤ x0) (hxb : x0 ≤ b) :
    Differentiable ℂ (finiteCorrection x0 b) := by
  have hsum : Differentiable ℂ (fun s : ℂ =>
      ∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (ForwardKernel.Adjoint.adjointKernel x0 s n -
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
end D5.S3.Arith.Robin.ForwardKernel.FiniteMellin
