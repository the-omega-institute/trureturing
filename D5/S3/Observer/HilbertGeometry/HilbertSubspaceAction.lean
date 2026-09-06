/- GID: D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction
   generality: G
   mirror-B: D5/B/S3/Observer/HilbertGeometry/HilbertSubspaceAction
   mirror-E: none(waiver:noncomputational-hilbert-variational-principle)
   anchors: []
   utility: none
   digest: Extended AC path action has the unique affine closed-subspace minimizer. -/

import D5.S3.Observer.HilbertGeometry.VectorPathDerivativeIntegrability
import D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal InnerProductSpace

namespace D5.S3.Observer.HilbertGeometry.HilbertSubspaceAction

open VectorPathDerivativeIntegrability HilbertPathFundamentalTheorem

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

private local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal 𝕜 H

/-- The nonnegative extended action; infinite quadratic energy is allowed.
The half-open interval differs from the closed interval only by a null endpoint. -/
def quadraticAction (f : ℝ → H) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖deriv f t‖ ^ 2)

/-- The source path class imposes only interval AC and the two endpoints. -/
def AdmissiblePath (M : ClosedSubmodule 𝕜 H) (x : H) (f : ℝ → H) : Prop :=
  AbsolutelyContinuousOnInterval f 0 1 ∧ f 0 ∈ M ∧ f 1 = x

/-- The affine path from the actual orthogonal projection to the target. -/
def affinePath (M : ClosedSubmodule 𝕜 H) (x : H) (t : ℝ) : H :=
  M.toSubmodule.starProjection x + t • (x - M.toSubmodule.starProjection x)

private lemma finite_action_integrable_sq {f : ℝ → H}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfin : quadraticAction (𝕜 := 𝕜) f ≠ ∞) :
    Integrable (fun t => ‖deriv f t‖ ^ 2) (volume.restrict (Ioc 0 1)) := by
  have hm := (absolutely_continuous_interval_integrable_deriv hf).1.aestronglyMeasurable
  apply (lintegral_ofReal_ne_top_iff_integrable (hm.norm.pow 2)
    (Eventually.of_forall fun _ => sq_nonneg _)).mp
  intro htop
  apply hfin
  change (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖deriv f t‖ ^ 2)) = ∞ at htop
  rw [quadraticAction, htop]
  simp

omit [CompleteSpace H] in
private lemma action_eq_of_integrable_sq {f : ℝ → H}
    (hf : Integrable (fun t => ‖deriv f t‖ ^ 2) (volume.restrict (Ioc 0 1))) :
    quadraticAction (𝕜 := 𝕜) f =
      ENNReal.ofReal ((∫ t in Ioc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) / 2) := by
  rw [quadraticAction, ← ofReal_integral_eq_lintegral_ofReal hf
    (Eventually.of_forall fun _ => sq_nonneg _), ENNReal.ofReal_div_of_pos (by norm_num)]
  simp [div_eq_mul_inv, mul_comm]

/-- Finite action supplies L2 velocity and the exact squared-velocity defect.
The derivative is the actual strong derivative almost everywhere, not a chosen velocity. -/
theorem finite_action_velocity_defect {f : ℝ → H}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfin : quadraticAction (𝕜 := 𝕜) f ≠ ∞) :
    MemLp (deriv f) 2 (volume.restrict (Ioc 0 1)) ∧
    Integrable (fun t => ‖deriv f t - (f 1 - f 0)‖ ^ 2)
      (volume.restrict (Ioc 0 1)) ∧
    (∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (deriv f t) t) ∧
    (∫ t in Ioc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) = ‖f 1 - f 0‖ ^ 2 +
      ∫ t in Ioc (0 : ℝ) 1, ‖deriv f t - (f 1 - f 0)‖ ^ 2 := by
  have hi := (absolutely_continuous_interval_integrable_deriv hf).1
  have hs := finite_action_integrable_sq (𝕜 := 𝕜) hf hfin
  have hLp := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr hs
  have hdLp := hLp.sub (memLp_const (f 1 - f 0))
  have hd := (memLp_two_iff_integrable_sq_norm hdLp.aestronglyMeasurable).mp hdLp
  have hder : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt f (deriv f t) t := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [absolutely_continuous_interval_ae_hasDerivAt hf] with t ht hmem
    exact ht (by simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      (Ioc_subset_Icc_self hmem))
  refine ⟨hLp, hd, hder, ?_⟩
  have hmean : (∫ t in Ioc (0 : ℝ) 1, deriv f t) = f 1 - f 0 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact absolutely_continuous_interval_integral_deriv_eq_sub hf right_mem_uIcc
  have hexpand : (∫ t in Ioc (0 : ℝ) 1, ‖deriv f t - (f 1 - f 0)‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) - ‖f 1 - f 0‖ ^ 2 := by
    have hp (t : ℝ) := norm_sub_sq_real (deriv f t) (f 1 - f 0)
    simp_rw [hp]
    rw [integral_add (f := fun t => ‖deriv f t‖ ^ 2 - 2 * ⟪deriv f t, f 1 - f 0⟫_ℝ)
      (g := fun _ => ‖f 1 - f 0‖ ^ 2)
      (hs.sub ((hi.inner_const (f 1 - f 0)).const_mul 2)) (integrable_const _),
      integral_sub (f := fun t => ‖deriv f t‖ ^ 2)
      (g := fun t => 2 * ⟪deriv f t, f 1 - f 0⟫_ℝ)
      hs ((hi.inner_const (f 1 - f 0)).const_mul 2),
      integral_const_mul]
    have hip : (∫ t in Ioc (0 : ℝ) 1, ⟪deriv f t, f 1 - f 0⟫_ℝ) =
        ⟪f 1 - f 0, f 1 - f 0⟫_ℝ := by
      simpa only [real_inner_comm, hmean] using integral_inner (𝕜 := ℝ) hi (f 1 - f 0)
    rw [hip]
    simp [measureReal_def]
    ring
  linarith

private lemma affine_hasDerivAt (M : ClosedSubmodule 𝕜 H) (x : H) (t : ℝ) :
    HasDerivAt (affinePath M x) (x - M.toSubmodule.starProjection x) t := by
  change HasDerivAt (fun s : ℝ => M.toSubmodule.starProjection x +
    s • (x - M.toSubmodule.starProjection x)) _ t
  simpa only [affinePath, id_eq, one_smul] using
    ((hasDerivAt_id t).smul_const (x - M.toSubmodule.starProjection x)).const_add
      (M.toSubmodule.starProjection x)

/-- The projection-based affine path belongs to the full AC class and attains the bound. -/
theorem affine_path_attainment (M : ClosedSubmodule 𝕜 H) (x : H) :
    AdmissiblePath M x (affinePath M x) ∧
    quadraticAction (𝕜 := 𝕜) (affinePath M x) =
      ENNReal.ofReal (‖x - M.toSubmodule.starProjection x‖ ^ 2 / 2) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · apply ContDiffOn.absolutelyContinuousOnInterval
      exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
    · change M.toSubmodule.starProjection x + (0 : ℝ) •
        (x - M.toSubmodule.starProjection x) ∈ M.toSubmodule
      simpa only [zero_smul, add_zero] using M.toSubmodule.starProjection_apply_mem x
    · simp [affinePath]
  · have hd : deriv (affinePath M x) = fun _ => x - M.toSubmodule.starProjection x :=
      funext fun t => (affine_hasDerivAt M x t).deriv
    simp [quadraticAction, hd, div_eq_mul_inv, mul_comm]

private lemma projection_defect (M : ClosedSubmodule 𝕜 H) (x y : H) (hy : y ∈ M) :
    ‖x - y‖ ^ 2 = ‖x - M.toSubmodule.starProjection x‖ ^ 2 +
      ‖M.toSubmodule.starProjection x - y‖ ^ 2 := by
  have heq : x - y = (x - M.toSubmodule.starProjection x) +
      (M.toSubmodule.starProjection x - y) := by abel
  rw [heq]
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (𝕜 := 𝕜) (x - M.toSubmodule.starProjection x) (M.toSubmodule.starProjection x - y)
    (M.toSubmodule.starProjection_inner_eq_zero x _
      (M.toSubmodule.sub_mem (M.toSubmodule.starProjection_apply_mem x) hy))

private lemma finite_action_bound_rigidity (M : ClosedSubmodule 𝕜 H) (x : H)
    {f : ℝ → H} (hf : AdmissiblePath M x f)
    (hfin : quadraticAction (𝕜 := 𝕜) f ≠ ∞) :
    ENNReal.ofReal (‖x - M.toSubmodule.starProjection x‖ ^ 2 / 2) ≤
        quadraticAction (𝕜 := 𝕜) f ∧
    (quadraticAction (𝕜 := 𝕜) f =
        ENNReal.ofReal (‖x - M.toSubmodule.starProjection x‖ ^ 2 / 2) →
      f 0 = M.toSubmodule.starProjection x ∧
      ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
        HasDerivAt f (x - M.toSubmodule.starProjection x) t) := by
  obtain ⟨hLp, hd, hder, hvariance⟩ := finite_action_velocity_defect (𝕜 := 𝕜) hf.1 hfin
  have hs := (memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).mp hLp
  have haction := action_eq_of_integrable_sq (𝕜 := 𝕜) hs
  have hprojection : ‖f 1 - f 0‖ ^ 2 = ‖x - M.toSubmodule.starProjection x‖ ^ 2 +
      ‖M.toSubmodule.starProjection x - f 0‖ ^ 2 := by
    rw [hf.2.2]
    exact projection_defect M x (f 0) hf.2.1
  rw [hprojection] at hvariance
  have hD : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖deriv f t - (f 1 - f 0)‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hP := sq_nonneg ‖M.toSubmodule.starProjection x - f 0‖
  have hE : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖deriv f t‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  constructor
  · rw [haction]
    apply ENNReal.ofReal_le_ofReal
    linarith
  · intro heq
    rw [haction] at heq
    have heqR := (ENNReal.ofReal_eq_ofReal_iff (div_nonneg hE (by norm_num))
      (div_nonneg (sq_nonneg _) (by norm_num))).mp heq
    have hstart : f 0 = M.toSubmodule.starProjection x := by
      have hn : ‖M.toSubmodule.starProjection x - f 0‖ ^ 2 = 0 := by linarith
      exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))).symm
    have hzero : (∫ t in Ioc (0 : ℝ) 1, ‖deriv f t - (f 1 - f 0)‖ ^ 2) = 0 := by
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun t => sq_nonneg ‖deriv f t - (f 1 - f 0)‖) hd).mp hzero
    refine ⟨hstart, ?_⟩
    filter_upwards [hae, hder] with t ht hdt
    have hv : deriv f t = f 1 - f 0 :=
      sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp ht))
    simpa only [hv, hf.2.2, hstart] using hdt

private lemma pointwise_of_constant_velocity {f : ℝ → H}
    (hf : AbsolutelyContinuousOnInterval f 0 1) {v : H}
    (hv : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f v t) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t = f 0 + t • v := by
  intro t ht
  have hftc := absolutely_continuous_interval_integral_deriv_eq_sub hf
    (by simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)
  have hv' := (ae_restrict_iff' measurableSet_Ioc).mp hv
  have hint : (∫ s in (0 : ℝ)..t, deriv f s) = t • v := by
    calc
      (∫ s in (0 : ℝ)..t, deriv f s) = ∫ _s in (0 : ℝ)..t, v := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hv'] with s hs hmem
        rw [uIoc_of_le ht.1] at hmem
        exact (hs ⟨hmem.1, hmem.2.trans ht.2⟩).deriv
      _ = t • v := by simp
  rw [hint] at hftc
  exact (eq_add_of_sub_eq hftc.symm).trans (add_comm _ _)

omit [CompleteSpace H] in
private lemma action_congr {f g : ℝ → H} (hfg : EqOn f g (Icc (0 : ℝ) 1)) :
    quadraticAction (𝕜 := 𝕜) f = quadraticAction (𝕜 := 𝕜) g := by
  have hd := (hfg.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  unfold quadraticAction
  congr 1
  apply lintegral_congr_ae
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [hd ht]

/-- Among all AC paths starting in a closed subspace and ending at `x`, the extended
quadratic action has the stated minimum. Equality characterizes the affine path
at every interval point, including both endpoints; infinite action is a separate case. -/
theorem absolutely_continuous_subspace_action_minimum_unique
    (M : ClosedSubmodule 𝕜 H) (x : H) :
    AdmissiblePath M x (affinePath M x) ∧
    quadraticAction (𝕜 := 𝕜) (affinePath M x) =
      ENNReal.ofReal (‖x - M.toSubmodule.starProjection x‖ ^ 2 / 2) ∧
    ∀ f : ℝ → H, AdmissiblePath M x f →
      ENNReal.ofReal (‖x - M.toSubmodule.starProjection x‖ ^ 2 / 2) ≤
          quadraticAction (𝕜 := 𝕜) f ∧
      (quadraticAction (𝕜 := 𝕜) f =
          ENNReal.ofReal (‖x - M.toSubmodule.starProjection x‖ ^ 2 / 2) ↔
        EqOn f (affinePath M x) (Icc 0 1)) := by
  obtain ⟨hadm, hatt⟩ := affine_path_attainment M x
  refine ⟨hadm, hatt, fun f hf => ?_⟩
  by_cases htop : quadraticAction (𝕜 := 𝕜) f = ∞
  · refine ⟨htop.symm ▸ le_top, ?_⟩
    constructor
    · intro heq
      exact False.elim (ENNReal.ofReal_ne_top (heq.symm.trans htop))
    · intro hfg
      exact (action_congr (𝕜 := 𝕜) hfg).trans hatt
  · obtain ⟨hle, hrigid⟩ := finite_action_bound_rigidity M x hf htop
    refine ⟨hle, ?_⟩
    constructor
    · intro heq
      obtain ⟨hstart, hv⟩ := hrigid heq
      intro t ht
      simpa only [hstart, affinePath] using pointwise_of_constant_velocity hf.1 hv t ht
    · intro hfg
      exact (action_congr (𝕜 := 𝕜) hfg).trans hatt

end D5.S3.Observer.HilbertGeometry.HilbertSubspaceAction
