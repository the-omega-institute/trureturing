/- GID: D5/S3/Geometry/Riemannian/GradientDissipation
   generality: G
   mirror-B: D5/B/S3/Geometry/Riemannian/GradientDissipation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Geometry.Manifold.ContMDiffMFDeriv, mathlib/module/Mathlib.Analysis.InnerProductSpace.Dual]
   utility: none
   digest: Canonical metric absolute continuity of smooth curves and Riesz-gradient dissipation. -/

import D5.S3.Geometry.Riemannian.ChartComparison
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import D5.S3.Geometry.Metric.MetricACSpeed
import D5.S3.Geometry.Riemannian.ACTangentSpeed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle Topology ContDiff ENNReal NNReal InnerProductSpace

noncomputable section
namespace Original172

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [hT2 : T2Space M] [hConnected : ConnectedSpace M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]

local notation "𝕀" => 𝓘(ℝ, E)
local notation "IR" => 𝓘(ℝ, ℝ)
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

include hT2 hConnected

/-- The Riesz representative for the given tangent inner product. -/
def actualGradient (V : M → ℝ) (p : M) : TangentSpace 𝕀 p :=
  (InnerProductSpace.toDual ℝ (TangentSpace 𝕀 p)).symm (mfderiv 𝕀 IR V p)

private theorem actualGradient_pairing (V : M → ℝ) (p : M)
    (w : TangentSpace 𝕀 p) :
    inner ℝ (actualGradient V p) w = mfderiv 𝕀 IR V p w := by
  exact InnerProductSpace.toDual_symm_apply

private theorem actual_gradient_flow_chain_rule (V : M → ℝ) (x : ℝ → M)
    (t : ℝ) (hV : MDifferentiableAt 𝕀 IR V (x t))
    (hx : MDifferentiableAt IR 𝕀 x t)
    (hflow : mfderiv IR 𝕀 x t 1 = -actualGradient V (x t)) :
    HasDerivAt (V ∘ x) (-(‖mfderiv IR 𝕀 x t 1‖ ^ 2)) t := by
  set_option backward.isDefEq.respectTransparency false in
    have hcomp : HasMFDerivAt IR IR (V ∘ x) t
        ((mfderiv 𝕀 IR V (x t)).comp (mfderiv IR 𝕀 x t)) :=
      hV.hasMFDerivAt.comp t hx.hasMFDerivAt
    have hfd : HasFDerivAt (V ∘ x)
        ((mfderiv 𝕀 IR V (x t)).comp (mfderiv IR 𝕀 x t)) t :=
      hcomp.hasFDerivAt
    have hd : HasDerivAt (V ∘ x)
        (mfderiv 𝕀 IR V (x t) (mfderiv IR 𝕀 x t 1)) t :=
      hfd.hasDerivAt
    have hp : mfderiv 𝕀 IR V (x t) (mfderiv IR 𝕀 x t 1) =
        -(‖mfderiv IR 𝕀 x t 1‖ ^ 2) := by
      rw [← actualGradient_pairing, hflow]
      simp only [inner_neg_right, real_inner_self_eq_norm_sq, norm_neg]
    exact hp ▸ hd

private theorem within_velocity_eq_velocity {T t : ℝ} (x : ℝ → M)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1 =
      mfderiv IR 𝕀 x t 1 := by
  rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Continuity concerns the closed-interval within velocity. The arbitrary
total extension of x need not have a two-sided derivative at either endpoint. -/
private theorem within_velocity_norm_continuous {T : ℝ} (hT : 0 < T)
    (x : ℝ → M) (hx : ContMDiffOn IR 𝕀 1 x (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t => ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖)
      (Icc (0 : ℝ) T) ∧
    ContinuousOn (fun t => ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖ ^ 2)
      (Icc (0 : ℝ) T) := by
  have hsec : Continuous
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle IR ℝ)) := by
    exact (tangentBundleModelSpaceHomeomorph IR).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have htm := hx.continuousOn_tangentMapWithin (by norm_num)
    (uniqueDiffOn_Icc hT).uniqueMDiffOn
  have hv : ContinuousOn
      (fun t => (⟨x t, mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1⟩ :
        TangentBundle 𝕀 M)) (Icc (0 : ℝ) T) := by
    exact htm.comp hsec.continuousOn (fun t ht => ht)
  have hs : ContinuousOn
      (fun t => ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖ ^ 2)
      (Icc (0 : ℝ) T) := by
    simpa only [real_inner_self_eq_norm_sq] using hv.inner_bundle hv
  refine ⟨?_, hs⟩
  simpa only [Real.sqrt_sq_eq_abs, abs_norm] using hs.sqrt

/-- S1, with exactly the original curve hypothesis and canonical metric.
The Lipschitz constant is constructed internally from compactness. -/
theorem S1_C1_to_actual_metric_AC {T : ℝ} (hT : 0 < T) (x : ℝ → M)
    (hx : ContMDiffOn IR 𝕀 1 x (Icc (0 : ℝ) T)) :
    letI : MetricSpace M := canonicalMetric (E := E) (M := M)
    AbsolutelyContinuousOnInterval x 0 T := by
  letI : MetricSpace M := canonicalMetric (E := E) (M := M)
  have hnorm := (within_velocity_norm_continuous hT x hx).1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hnorm
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hK : ∀ t ∈ Icc (0 : ℝ) T,
      ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖ ≤ (K : ℝ) := by
    intro t ht
    have hc : ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖ ≤ C := by
      simpa only [norm_norm] using hC t ht
    exact hc.trans (le_max_left C 0)
  have hordered : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      edist (x a) (x b) ≤ (K : ℝ≥0∞) * edist a b := by
    intro a ha b hb hab
    have hed : edist a b = ENNReal.ofReal (b - a) := by
      rw [edist_dist, Real.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hab)]
    calc
      edist (x a) (x b) = riemannianEDist 𝕀 (x a) (x b) :=
        canonicalMetric_edist (E := E) (x a) (x b)
      _ ≤ pathELength 𝕀 x a b :=
        riemannianEDist_le_pathELength (I := 𝕀)
          (hx.mono (Icc_subset_Icc ha.1 hb.2)) rfl rfl hab
      _ = ∫⁻ t in Ioo a b, ‖mfderiv IR 𝕀 x t 1‖ₑ :=
        pathELength_eq_lintegral_mfderiv_Ioo (I := 𝕀)
      _ ≤ ∫⁻ _t in Ioo a b, (K : ℝ≥0∞) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro t ht
        have ht0 : t ∈ Ioo (0 : ℝ) T :=
          ⟨lt_of_le_of_lt ha.1 ht.1, lt_of_lt_of_le ht.2 hb.2⟩
        have hs : ‖mfderiv IR 𝕀 x t 1‖ ≤ (K : ℝ) := by
          rw [← within_velocity_eq_velocity x ht0]
          exact hK t ⟨ht0.1.le, ht0.2.le⟩
        change (‖mfderiv IR 𝕀 x t 1‖₊ : ℝ≥0∞) ≤ (K : ℝ≥0∞)
        exact_mod_cast hs
      _ = (K : ℝ≥0∞) * edist a b := by
        rw [setLIntegral_const, Real.volume_Ioo, hed]
  have hLip : LipschitzOnWith K x (uIcc (0 : ℝ) T) := by
    rw [uIcc_of_le hT.le]
    intro a ha b hb
    rcases le_total a b with hab | hba
    · exact hordered a ha b hb hab
    · simpa only [edist_comm] using hordered b hb a ha hba
  exact hLip.absolutelyContinuousOnInterval

/-- S2: actual speed and speed squared are integrable, and the actual Riesz
gradient ODE gives the dissipation identity. Only within derivatives occur in
the closed-interval ODE premise. -/
theorem S2_dissipation {T : ℝ} (hT : 0 < T) (V : M → ℝ) (x : ℝ → M)
    (hV : ContMDiff 𝕀 IR 1 V)
    (hx : ContMDiffOn IR 𝕀 1 x (Icc (0 : ℝ) T))
    (hflow : ∀ t ∈ Icc (0 : ℝ) T,
      mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1 = -actualGradient V (x t)) :
    IntervalIntegrable (fun t => ‖mfderiv IR 𝕀 x t 1‖) volume 0 T ∧
    IntervalIntegrable (fun t => ‖mfderiv IR 𝕀 x t 1‖ ^ 2) volume 0 T ∧
    V (x 0) - V (x T) = ∫ t in (0 : ℝ)..T, ‖mfderiv IR 𝕀 x t 1‖ ^ 2 := by
  obtain ⟨hnorm, hsquare⟩ := within_velocity_norm_continuous hT x hx
  have hiw : IntervalIntegrable
      (fun t => ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖) volume 0 T :=
    hnorm.intervalIntegrable_of_Icc hT.le
  have hiw2 : IntervalIntegrable
      (fun t => ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖ ^ 2) volume 0 T :=
    hsquare.intervalIntegrable_of_Icc hT.le
  have hi : IntervalIntegrable (fun t => ‖mfderiv IR 𝕀 x t 1‖) volume 0 T := by
    apply hiw.congr_uIoo
    intro t ht
    rw [uIoo_of_le hT.le] at ht
    change ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖ =
      ‖mfderiv IR 𝕀 x t 1‖
    exact congrArg norm (within_velocity_eq_velocity x ht)
  have hi2 : IntervalIntegrable (fun t => ‖mfderiv IR 𝕀 x t 1‖ ^ 2) volume 0 T := by
    apply hiw2.congr_uIoo
    intro t ht
    rw [uIoo_of_le hT.le] at ht
    change ‖mfderivWithin IR 𝕀 x (Icc (0 : ℝ) T) t 1‖ ^ 2 =
      ‖mfderiv IR 𝕀 x t 1‖ ^ 2
    exact congrArg (fun v : TangentSpace 𝕀 (x t) => ‖v‖ ^ 2)
      (within_velocity_eq_velocity x ht)
  refine ⟨hi, hi2, ?_⟩
  have hc : ContinuousOn (V ∘ x) (Icc (0 : ℝ) T) :=
    hV.continuous.comp_continuousOn hx.continuousOn
  have hd : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (V ∘ x) (-(‖mfderiv IR 𝕀 x t 1‖ ^ 2)) t := by
    intro t ht
    have hxt : MDifferentiableAt IR 𝕀 x t :=
      (hx.mdifferentiableOn (by norm_num) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hf : mfderiv IR 𝕀 x t 1 = -actualGradient V (x t) := by
      rw [← within_velocity_eq_velocity x ht]
      exact hflow t ⟨ht.1.le, ht.2.le⟩
    exact actual_gradient_flow_chain_rule V x t
      (hV.mdifferentiable (by norm_num) (x t)) hxt hf
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hT.le hc hd hi2.neg
  rw [intervalIntegral.integral_neg] at hftc
  change -(∫ t in (0 : ℝ)..T, ‖mfderiv IR 𝕀 x t 1‖ ^ 2) =
    V (x T) - V (x 0) at hftc
  linarith

/-- Actual R3 for the original canonical metric and actual tangent velocity.
In particular, speed integrability and the derivative identity are conclusions.
The exact increments and endpoint estimate use the SAME speed integral. -/
theorem actual_AC_speed_variation_length {T : ℝ} (hT : 0 < T)
    (z : ℝ → M)
    (hz : letI : MetricSpace M := canonicalMetric (E := E) (M := M)
      AbsolutelyContinuousOnInterval z 0 T) :
    letI : MetricSpace M := canonicalMetric (E := E) (M := M)
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), MDifferentiableAt IR 𝕀 z t) ∧
    AEMeasurable (fun t => ‖mfderiv IR 𝕀 z t 1‖ₑ)
      (volume.restrict (Icc (0 : ℝ) T)) ∧
    IntervalIntegrable (fun t => ‖mfderiv IR 𝕀 z t 1‖) volume 0 T ∧
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      deriv (variationOnFromTo z (Icc 0 T) 0) t = ‖mfderiv IR 𝕀 z t 1‖) ∧
    pathELength 𝕀 z 0 T = eVariationOn z (Icc 0 T) ∧
    pathELength 𝕀 z 0 T < ⊤ ∧
    riemannianEDist 𝕀 (z 0) (z T) ≤ pathELength 𝕀 z 0 T ∧
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      (∫ t in a..b, ‖mfderiv IR 𝕀 z t 1‖) = (eVariationOn z (Icc a b)).toReal) ∧
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      dist (z a) (z b) ≤ ∫ t in a..b, ‖mfderiv IR 𝕀 z t 1‖) := by
  letI : MetricSpace M := canonicalMetric (E := E) (M := M)
  obtain ⟨_partition, hae, hmeas⟩ :=
    actual_chart_AC_tangent_and_metric_speed (E := E) (M := M) (T := T) hT z hz
  have hrealmeas : AEMeasurable (fun t => ‖mfderiv IR 𝕀 z t 1‖)
      (volume.restrict (Icc (0 : ℝ) T)) := by
    simpa [← ofReal_norm] using hmeas.ennreal_toReal
  obtain ⟨hint, hderiv, hlin, hincrements, hchords⟩ :=
    metric_AC_speed_variation_bridge hT z hz
      (fun t => ‖mfderiv IR 𝕀 z t 1‖) (fun t => norm_nonneg _)
      hrealmeas.aestronglyMeasurable (hae.mono (fun t ht => ht.2.2))
  have hlength : pathELength 𝕀 z 0 T = eVariationOn z (Icc 0 T) := by
    rw [pathELength_eq_lintegral_mfderiv_Icc]
    simpa only [ofReal_norm] using hlin
  have hBV : BoundedVariationOn z (Icc (0 : ℝ) T) := by
    have h := metric_AC_boundedVariationOn (Y := M) (f := z) (a := 0) (b := T) hz
    rwa [uIcc_of_le hT.le] at h
  have hdist : riemannianEDist 𝕀 (z 0) (z T) ≤ pathELength 𝕀 z 0 T := by
    rw [← canonicalMetric_edist (E := E), hlength]
    exact eVariationOn.edist_le z ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩
  exact ⟨hae.mono (fun t ht => ht.1), hmeas, hint, hderiv, hlength,
    hlength.symm ▸ (lt_top_iff_ne_top.mpr hBV), hdist, hincrements, hchords⟩

def kineticAction (z : ℝ → M) (T : ℝ) : ℝ≥0∞ :=
  (∫⁻ t in Icc (0:ℝ) T, ‖mfderiv IR 𝕀 z t 1‖ₑ ^ 2) / 2

def shortestConnector (z : ℝ → M) (T : ℝ) : Prop :=
  ∀ y : ℝ → M, ContMDiffOn IR 𝕀 1 y (Icc (0:ℝ) 1) →
    y 0 = z 0 → y 1 = z T →
    pathELength 𝕀 z 0 T ≤ pathELength 𝕀 y 0 1

/-- A consumed finite-energy transport calculation, not an extra hypothesis
of the gradient-flow or shortest-curve targets. -/
theorem actual_length_energy_real {T : ℝ} (hT : 0 < T) (z : ℝ → M)
    (hz : letI : MetricSpace M := canonicalMetric (E:=E) (M:=M)
      AbsolutelyContinuousOnInterval z 0 T)
    (hi2 : IntervalIntegrable (fun t => ‖mfderiv IR 𝕀 z t 1‖^2) volume 0 T) :
    pathELength 𝕀 z 0 T < ⊤ ∧
    (pathELength 𝕀 z 0 T).toReal = ∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖ ∧
    kineticAction (E := E) z T < ⊤ ∧
    (kineticAction (E := E) z T).toReal = (∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖^2)/2 ∧
    (pathELength 𝕀 z 0 T).toReal^2 ≤
      T * (∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖^2) := by
  letI : MetricSpace M := canonicalMetric (E:=E) (M:=M)
  obtain ⟨_, _, hi, _, hLV, hL, _, hinc, _⟩ :=
    actual_AC_speed_variation_length hT z hz
  have hLi : (pathELength 𝕀 z 0 T).toReal =
      ∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖ := by
    rw [hLV]
    exact (hinc 0 ⟨le_rfl,hT.le⟩ T ⟨hT.le,le_rfl⟩ hT.le).symm
  have hi2c := (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hi2
  have hnn : 0 ≤ ∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖^2 :=
    intervalIntegral.integral_nonneg hT.le (fun t _ht => sq_nonneg _)
  have hE : (∫⁻ t in Icc (0:ℝ) T, ‖mfderiv IR 𝕀 z t 1‖ₑ^2) =
      ENNReal.ofReal (∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖^2) := by
    calc
      _ = ∫⁻ t in Icc (0:ℝ) T, ENNReal.ofReal (‖mfderiv IR 𝕀 z t 1‖^2) := by
        apply lintegral_congr
        intro t
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ = ENNReal.ofReal (∫ t in Icc (0:ℝ) T, ‖mfderiv IR 𝕀 z t 1‖^2) :=
        (ofReal_integral_eq_lintegral_ofReal hi2c
          (Eventually.of_forall (fun t => sq_nonneg _))).symm
      _ = _ := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hT.le]
  have hA : kineticAction (E := E) z T < ⊤ := by
    simp only [kineticAction, hE]
    finiteness
  have hAi : (kineticAction (E := E) z T).toReal =
      (∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖^2)/2 := by
    simp [kineticAction, hE, ENNReal.toReal_div, ENNReal.toReal_ofReal hnn]
  refine ⟨hL, hLi, hA, hAi, ?_⟩
  have hm : MemLp (fun t => ‖mfderiv IR 𝕀 z t 1‖) 2
      (volume.restrict (Ioc (0:ℝ) T)) :=
    (memLp_two_iff_integrable_sq hi.1.aestronglyMeasurable).mpr hi2.1
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc (0:ℝ) T)) Real.HolderConjugate.two_two
    (f := fun _ : ℝ => 1) (g := fun t => ‖mfderiv IR 𝕀 z t 1‖)
    (Eventually.of_forall (fun _ => zero_le_one))
    (Eventually.of_forall (fun t => norm_nonneg _)) (memLp_const (1:ℝ)) (by norm_num; exact hm)
  have hroot : (∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖) ≤
      Real.sqrt T * Real.sqrt (∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖^2) := by
    simpa [intervalIntegral.integral_of_le hT.le, Real.rpow_two,
      Real.sqrt_eq_rpow, Real.volume_Ioc, hT.le] using hH
  have hleft0 : 0 ≤ ∫ t in (0:ℝ)..T, ‖mfderiv IR 𝕀 z t 1‖ :=
    intervalIntegral.integral_nonneg hT.le (fun t _ht => norm_nonneg _)
  have hsq := pow_le_pow_left₀ hleft0 hroot 2
  rw [mul_pow, Real.sq_sqrt hT.le, Real.sq_sqrt hnn, ← hLi] at hsq
  exact hsq

end Original172
