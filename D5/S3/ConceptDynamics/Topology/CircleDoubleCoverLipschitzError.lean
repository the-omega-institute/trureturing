/- GID: D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp normalized chord-error bound for intrinsic-Lipschitz circle selectors. -/

/- proof_shape: result: content
   escape_witness: odd winding forces weighted phase variation, and the piecewise
     lift attains the resulting bound at every L at least one half.
   admission_basis: escape-witness (issue #10461) -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped Interval NNReal

namespace D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError

noncomputable section

local instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

private def weight (x : ℝ) : ℝ := 2 - 2 * Real.cos x

private def primitive (x : ℝ) : ℝ := 2 * (x - Real.sin x)

private theorem weight_nonneg (x : ℝ) : 0 ≤ weight x := by
  dsimp [weight]
  linarith [Real.cos_le_one x]

private theorem weight_le_four (x : ℝ) : weight x ≤ 4 := by
  dsimp [weight]
  linarith [Real.neg_one_le_cos x]

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (weight x) x := by
  change HasDerivAt (fun y : ℝ => 2 * (y - Real.sin y))
    (2 - 2 * Real.cos x) x
  simpa [primitive, weight, mul_sub, mul_comm] using
    (((hasDerivAt_id x).sub (Real.hasDerivAt_sin x)).const_mul (2 : ℝ))

private theorem primitive_lipschitz : LipschitzWith 4 primitive := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (primitive_hasDerivAt x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, NNReal.coe_ofNat, (primitive_hasDerivAt x).deriv,
    Real.norm_eq_abs, abs_of_nonneg (weight_nonneg x)] using weight_le_four x

private theorem weighted_variation (K : ℝ≥0) (φ : ℝ → ℝ)
    (a b : ℝ)
    (hφglob : ∃ K', LipschitzOnWith K' φ (uIcc a b))
    (hφac : AbsolutelyContinuousOnInterval φ a b)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc a b → |deriv φ t| ≤ K)
    (hab : a ≤ b) :
    |primitive (φ b) - primitive (φ a)| ≤
      K * ∫ t in a..b, weight (φ t) := by
  obtain ⟨K', hφglob⟩ := hφglob
  have hcomp : AbsolutelyContinuousOnInterval (primitive ∘ φ) a b :=
    (primitive_lipschitz.comp_lipschitzOnWith hφglob).absolutelyContinuousOnInterval
  have hweight : Continuous weight := by
    unfold weight
    fun_prop
  have hwcont : ContinuousOn (fun t => weight (φ t)) (uIcc a b) :=
    (hweight.continuousOn : ContinuousOn weight univ).comp hφac.continuousOn
      (fun _ _ => mem_univ _)
  have hderiv_comp : ∀ᵐ t : ℝ, t ∈ Icc a b →
      |deriv (primitive ∘ φ) t| ≤ K * weight (φ t) := by
    filter_upwards [hφac.ae_differentiableAt, hderiv] with t ht hdt hmem
    rw [deriv_comp t (primitive_hasDerivAt (φ t)).differentiableAt (ht (by simpa [uIcc_of_le hab] using hmem)),
      (primitive_hasDerivAt (φ t)).deriv, abs_mul]
    rw [abs_of_nonneg (weight_nonneg (φ t))]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right (hdt hmem) (weight_nonneg (φ t))
  change |(primitive ∘ φ) b - (primitive ∘ φ) a| ≤
    K * ∫ t in a..b, weight (φ t)
  rw [← hcomp.integral_deriv_eq_sub]
  calc
    |∫ t in a..b, deriv (primitive ∘ φ) t| ≤
        ∫ t in a..b, |deriv (primitive ∘ φ) t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, K * weight (φ t) :=
      intervalIntegral.integral_mono_ae_restrict hab
        hcomp.intervalIntegrable_deriv.abs
        (hwcont.intervalIntegrable.const_mul (K : ℝ))
        ((ae_restrict_iff' measurableSet_Icc).2 hderiv_comp)
    _ = K * ∫ t in a..b, weight (φ t) := by
      rw [intervalIntegral.integral_const_mul]

private theorem weighted_variation_of_nonzero_winding (K : ℝ≥0)
    (φ : ℝ → ℝ) (a b : ℝ)
    (hφglob : ∃ K', LipschitzOnWith K' φ (uIcc a b))
    (hφac : AbsolutelyContinuousOnInterval φ a b)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc a b → |deriv φ t| ≤ K)
    (hab : a ≤ b) (n : ℤ) (hn : n ≠ 0)
    (hwind : φ b = φ a + n * (2 * Real.pi)) :
    4 * Real.pi ≤ K * ∫ t in a..b, weight (φ t) := by
  have hprimitive : primitive (φ b) - primitive (φ a) =
      (n : ℝ) * (4 * Real.pi) := by
    rw [hwind, primitive, primitive, Real.sin_add_int_mul_two_pi]
    push_cast
    ring
  have hnint : (1 : ℤ) ≤ |n| := by
    rcases lt_or_gt_of_ne hn with hnneg | hnpos
    · rw [abs_of_neg hnneg]
      omega
    · rw [abs_of_pos hnpos]
      omega
  have hnreal : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hnint
  have hvar := weighted_variation K φ a b hφglob hφac hderiv hab
  rw [hprimitive] at hvar
  calc
    4 * Real.pi = (4 * Real.pi) * 1 := by ring
    _ ≤ (4 * Real.pi) * |(n : ℝ)| :=
      mul_le_mul_of_nonneg_left hnreal (by positivity)
    _ = |(n : ℝ) * (4 * Real.pi)| := by
      simp only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      ring
    _ ≤ K * ∫ t in a..b, weight (φ t) := hvar

private theorem lift_locally_lipschitz {T : ℝ} (hT : 0 < T) (L : ℝ≥0)
    (s : AddCircle T → AddCircle T) (hs : LipschitzWith L s)
    (θ : ℝ → ℝ) (hθcont : Continuous θ)
    (hθproj : ∀ t, (θ t : AddCircle T) = s (t : AddCircle T)) :
    ∀ t, ∃ U ∈ 𝓝 t, LipschitzOnWith L θ U := by
  intro t
  have htθ : θ ⁻¹' Metric.ball (θ t) (T / 4) ∈ 𝓝 t :=
    hθcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith))
  let U : Set ℝ := Metric.ball t (T / 4) ∩ θ ⁻¹' Metric.ball (θ t) (T / 4)
  have hU : U ∈ 𝓝 t :=
    inter_mem (Metric.ball_mem_nhds _ (by linarith)) htθ
  refine ⟨U, hU, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hxdom : dist x t < T / 4 := hx.1
  have hydom : dist y t < T / 4 := hy.1
  have hxθ : dist (θ x) (θ t) < T / 4 := hx.2
  have hyθ : dist (θ y) (θ t) < T / 4 := hy.2
  rw [Real.dist_eq] at hxdom hydom hxθ hyθ
  have hxy : |x - y| < T / 2 := by
    have htri := dist_triangle x t y
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at htri
    have hydom' : |t - y| < T / 4 := by simpa [abs_sub_comm] using hydom
    exact (by linarith [htri, hxdom, hydom'])
  have hθxy : |θ x - θ y| < T / 2 := by
    have htri := dist_triangle (θ x) (θ t) (θ y)
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at htri
    have hyθ' : |θ t - θ y| < T / 4 := by simpa [abs_sub_comm] using hyθ
    exact (by linarith [htri, hxθ, hyθ'])
  have hnorm_domain : dist (x : AddCircle T) (y : AddCircle T) = |x - y| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub,
      AddCircle.norm_coe_eq_abs_iff T (ne_of_gt hT)]
    rw [abs_of_pos hT]
    exact hxy.le
  have hcircle_lift : dist (θ x : AddCircle T) (θ y : AddCircle T) = |θ x - θ y| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub,
      AddCircle.norm_coe_eq_abs_iff T (ne_of_gt hT)]
    rw [abs_of_pos hT]
    exact hθxy.le
  rw [Real.dist_eq]
  calc
    |θ x - θ y| = dist ((θ x : AddCircle T)) ((θ y : AddCircle T)) := hcircle_lift.symm
    _ = dist (s (x : AddCircle T)) (s (y : AddCircle T)) := by rw [hθproj x, hθproj y]
    _ ≤ L * dist (x : AddCircle T) (y : AddCircle T) := hs.dist_le_mul _ _
    _ = L * |x - y| := by rw [hnorm_domain]

private theorem lift_derivative_data {T : ℝ} (hT : 0 < T) (L : ℝ≥0)
    (s : AddCircle T → AddCircle T) (hs : LipschitzWith L s)
    (θ : ℝ → ℝ) (hθcont : Continuous θ)
    (hθproj : ∀ t, (θ t : AddCircle T) = s (t : AddCircle T)) :
    ∃ Kθ, LipschitzOnWith Kθ θ (uIcc 0 T) ∧
      AbsolutelyContinuousOnInterval θ 0 T ∧
      ∀ᵐ t : ℝ, t ∈ Icc 0 T → |deriv θ t| ≤ L := by
  have hlocal : LocallyLipschitzOn (Icc 0 T) θ := by
    intro t ht
    obtain ⟨U, hU, hUθ⟩ := lift_locally_lipschitz hT L s hs θ hθcont hθproj t
    refine ⟨L, U ∩ Icc 0 T,
      inter_mem (mem_nhdsWithin_of_mem_nhds hU) self_mem_nhdsWithin, ?_⟩
    exact hUθ.mono inter_subset_left
  obtain ⟨Kθ, hKθ⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hKθu : LipschitzOnWith Kθ θ (uIcc 0 T) := by
    simpa [uIcc_of_le (le_of_lt hT)] using hKθ
  refine ⟨Kθ, hKθu, hKθu.absolutelyContinuousOnInterval, ?_⟩
  filter_upwards [] with t hmem
  obtain ⟨U, hU, hUθ⟩ := lift_locally_lipschitz hT L s hs θ hθcont hθproj t
  have hd := norm_deriv_le_of_lipschitzOn hU hUθ
  simpa [Real.norm_eq_abs] using hd

private theorem circle_continuous_lift {T : ℝ} (hT : 0 < T) (L : ℝ≥0)
    (s : AddCircle T → AddCircle T) (hs : LipschitzWith L s) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, (θ t : AddCircle T) = s (t : AddCircle T)) ∧
      ∃ k : ℤ, θ T = θ 0 + (k : ℝ) * T := by
  letI : Fact (0 < T) := ⟨hT⟩
  let f : C(ℝ, AddCircle T) :=
    { toFun := fun t => s (t : AddCircle T)
      continuous_toFun := hs.continuous.comp (AddCircle.continuous_mk' T) }
  obtain ⟨θ₀, hθ₀⟩ :=
    QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples T) (s (0 : AddCircle T))
  obtain ⟨θ, hθ⟩ :=
    (AddCircle.isCoveringMap_coe T).existsUnique_continuousMap_lifts f 0 θ₀ (by
      simpa [f] using hθ₀)
  have hproj : ∀ t, (θ t : AddCircle T) = s (t : AddCircle T) := by
    intro t
    have h := congrFun hθ.1.2 t
    simpa [f, Function.comp_def] using h
  have hTzero : (T : AddCircle T) = 0 := by
    exact (AddCircle.coe_eq_zero_iff T).2 ⟨1, by simp⟩
  have hendproj : (θ T : AddCircle T) = (θ 0 : AddCircle T) := by
    rw [hproj T, hproj 0, hTzero]
    simp
  have hdiff : ((θ T - θ 0 : ℝ) : AddCircle T) = 0 := by
    rw [AddCircle.coe_sub, hendproj, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff T).mp hdiff
  refine ⟨θ, θ.continuous, hproj, k, ?_⟩
  have hk' : θ T - θ 0 = (k : ℝ) * T := by
    simpa [zsmul_eq_mul] using hk.symm
  linarith

private theorem circle_weighted_bound (L : ℝ≥0)
    (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi))
    (hs : LipschitzWith L s) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, (θ t : AddCircle (2 * Real.pi)) = s (t : AddCircle (2 * Real.pi))) ∧
      ∃ k : ℤ, θ (2 * Real.pi) = θ 0 + (k : ℝ) * (2 * Real.pi) ∧
        4 * Real.pi ≤ (2 * (L : ℝ) + 1) *
          ∫ t in (0 : ℝ)..(2 * Real.pi), weight (2 * θ t - t) := by
  obtain ⟨θ, hθcont, hθproj, k, hend⟩ :=
    circle_continuous_lift (by positivity) L s hs
  obtain ⟨Kθ, hKθ, hθac, hθderiv⟩ :=
    lift_derivative_data (by positivity) L s hs θ hθcont hθproj
  let φ : ℝ → ℝ := fun t => 2 * θ t - t
  have hφglob : ∃ Kφ, LipschitzOnWith Kφ φ (uIcc 0 (2 * Real.pi)) := by
    refine ⟨2 * Kθ + 1, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hθxy := hKθ.dist_le_mul x hx y hy
    rw [Real.dist_eq, Real.dist_eq] at hθxy
    rw [Real.dist_eq]
    calc
      |φ x - φ y| = |2 * (θ x - θ y) - (x - y)| := by
        congr 1
        dsimp [φ]
        ring
      _ ≤ |2 * (θ x - θ y)| + |x - y| := by
        simpa [abs_sub_comm] using (abs_sub_le (2 * (θ x - θ y)) 0 (x - y))
      _ = 2 * |θ x - θ y| + |x - y| := by
        rw [abs_mul, abs_two]
      _ ≤ 2 * ((Kθ : ℝ) * |x - y|) + |x - y| := by
        gcongr
      _ = ((2 * Kθ + 1 : ℝ≥0) : ℝ) * |x - y| := by
        norm_num
        ring
  have hφac : AbsolutelyContinuousOnInterval φ 0 (2 * Real.pi) := by
    obtain ⟨Kφ, hKφ⟩ := hφglob
    exact hKφ.absolutelyContinuousOnInterval
  have hφderiv : ∀ᵐ t : ℝ, t ∈ Icc 0 (2 * Real.pi) →
      |deriv φ t| ≤ (2 * (L : ℝ) + 1) := by
    filter_upwards [hθac.ae_differentiableAt, hθderiv] with t ht hdt hmem
    have hθhas : HasDerivAt θ (deriv θ t) t :=
      (ht (by simpa [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using hmem)).hasDerivAt
    have hφhas : HasDerivAt φ (2 * deriv θ t - 1) t := by
      exact ((hθhas.const_mul (2 : ℝ)).sub (hasDerivAt_id t)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun _ => rfl))
    have hφeq := hφhas.deriv
    rw [hφeq]
    calc
      |2 * deriv θ t - 1| ≤ |2 * deriv θ t| + |1| := by
        simpa using (abs_sub_le (2 * deriv θ t) 0 1)
      _ = 2 * |deriv θ t| + 1 := by rw [abs_mul, abs_two, abs_one]
      _ ≤ 2 * (L : ℝ) + 1 := by gcongr; exact hdt hmem
  have hwind : φ (2 * Real.pi) = φ 0 + ((2 * k - 1 : ℤ) : ℝ) * (2 * Real.pi) := by
    dsimp [φ]
    rw [hend]
    push_cast
    ring
  have hn : (2 * k - 1 : ℤ) ≠ 0 := by omega
  have hvar := weighted_variation_of_nonzero_winding
    (2 * L + 1) φ 0 (2 * Real.pi) hφglob hφac hφderiv (by positivity)
    (2 * k - 1) hn hwind
  refine ⟨θ, hθcont, hθproj, k, hend, ?_⟩
  simpa [φ] using hvar

/-- Squared complex chord error of a circle-valued selector under squaring. -/
def circle_error
    (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi))
    (x : AddCircle (2 * Real.pi)) : ℝ :=
  ‖((AddCircle.toCircle (2 • s x) : Circle) : ℂ) -
    ((AddCircle.toCircle x : Circle) : ℂ)‖ ^ 2

private theorem circle_exp_sub_sq (u v : ℝ) :
    ‖(Circle.exp u : ℂ) - Circle.exp v‖ ^ 2 = 2 - 2 * Real.cos (u - v) := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp [Circle.coe_exp, Complex.normSq_eq_norm_sq, Real.cos_sub]
  ring

private theorem circle_error_on_lift
    (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi))
    (θ t : ℝ)
    (hθproj : (θ : AddCircle (2 * Real.pi)) = s (t : AddCircle (2 * Real.pi))) :
    circle_error s (t : AddCircle (2 * Real.pi)) = weight (2 * θ - t) := by
  have hsθ : 2 • s (t : AddCircle (2 * Real.pi)) =
      2 • (θ : AddCircle (2 * Real.pi)) := congrArg (fun z => 2 • z) hθproj.symm
  rw [circle_error, hsθ, AddCircle.toCircle_nsmul, AddCircle.toCircle_apply_mk,
    AddCircle.toCircle_apply_mk]
  norm_num
  rw [← Complex.exp_nat_mul _ 2]
  have hfirst : Complex.exp (↑2 * (↑θ * Complex.I)) =
      (Circle.exp (2 * θ) : ℂ) := by
    rw [Circle.coe_exp]
    congr 1
    push_cast
    ring
  have hsecond : Complex.exp (↑t * Complex.I) = (Circle.exp t : ℂ) := Circle.coe_exp t
  norm_num
  rw [hfirst, hsecond]
  simpa [weight] using circle_exp_sub_sq (2 * θ) t

private theorem circle_lipschitz_error_lower_bound [Fact (0 < (2 * Real.pi : ℝ))] (L : ℝ≥0)
    (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi))
    (hs : LipschitzWith L s) :
    2 / (2 * (L : ℝ) + 1) ≤
      ∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle := by
  obtain ⟨θ, _, hθproj, _, _, hbound⟩ := circle_weighted_bound L s hs
  have hinter :
      (∫ t in (0 : ℝ)..(2 * Real.pi), circle_error s (t : AddCircle (2 * Real.pi))) =
        ∫ t in (0 : ℝ)..(2 * Real.pi), weight (2 * θ t - t) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t _ => circle_error_on_lift s (θ t) t (hθproj t))
  have hbound' : 4 * Real.pi ≤
      (2 * (L : ℝ) + 1) *
        ∫ t in (0 : ℝ)..(2 * Real.pi), circle_error s (t : AddCircle (2 * Real.pi)) := by
    rw [hinter]
    exact hbound
  have hpre := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 (circle_error s)
  have hhaar := AddCircle.integral_haarAddCircle (f := circle_error s)
  have hhaar' :
      (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle) =
        (2 * Real.pi)⁻¹ *
          ∫ t in (0 : ℝ)..(2 * Real.pi), circle_error s (t : AddCircle (2 * Real.pi)) := by
    rw [hhaar, smul_eq_mul, ← hpre]
    simp
  rw [hhaar']
  rw [inv_mul_eq_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) + 1)
    (by positivity : (0 : ℝ) < 2 * Real.pi)).2
  nlinarith [hbound']

private def sharp_a (L : ℝ≥0) : ℝ := (2 * Real.pi) / (2 * (L : ℝ) + 1)

private def sharp_b (L : ℝ≥0) : ℝ := 2 * Real.pi - sharp_a L

private def sharp_theta (L : ℝ≥0) (t : ℝ) : ℝ :=
  if t ≤ sharp_b L then t / 2 else (L : ℝ) * (2 * Real.pi - t)

private def sharp_map [Fact (0 < (2 * Real.pi : ℝ))] (L : ℝ≥0) :
    AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi) :=
  AddCircle.liftIco (2 * Real.pi) 0 (fun t => (sharp_theta L t : AddCircle (2 * Real.pi)))

private theorem sharp_theta_lipschitzOn
    (L : ℝ≥0) (hL : (1 / 2 : ℝ) ≤ (L : ℝ)) :
    LipschitzOnWith L (sharp_theta L) (Icc 0 (2 * Real.pi)) := by
  have hden : 0 < 2 * (L : ℝ) + 1 := by positivity
  have ha : 0 < sharp_a L := by
    dsimp [sharp_a]
    positivity
  have hab : sharp_a L ≤ 2 * Real.pi := by
    dsimp [sharp_a]
    apply (div_le_iff₀ hden).2
    nlinarith [Real.pi_pos]
  have hb : 0 ≤ sharp_b L := by
    dsimp [sharp_b]
    linarith
  have hseam : (sharp_b L) / 2 = (L : ℝ) * sharp_a L := by
    dsimp [sharp_b, sharp_a]
    field_simp [ne_of_gt hden]
    ring
  have hsum : sharp_b L + sharp_a L = 2 * Real.pi := by
    dsimp [sharp_b]
    ring
  refine LipschitzOnWith.of_dist_le_mul ?_
  have hforward : ∀ ⦃x y : ℝ⦄, x ∈ Icc 0 (2 * Real.pi) →
      y ∈ Icc 0 (2 * Real.pi) → x ≤ y →
        dist (sharp_theta L x) (sharp_theta L y) ≤ L * dist x y := by
    intro x y hx hy hxy
    rw [Real.dist_eq, Real.dist_eq]
    by_cases hyb : y ≤ sharp_b L
    · have hxb : x ≤ sharp_b L := hxy.trans hyb
      simp [sharp_theta, hxb, hyb]
      rw [show x / 2 - y / 2 = (x - y) / 2 by ring, abs_div,
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      nlinarith [hL]
    · by_cases hxb : sharp_b L < x
      · simp [sharp_theta, hxb, hyb]
        have : 0 ≤ y - x := sub_nonneg.mpr hxy
        simp [not_le_of_gt hxb]
        have heq : (L : ℝ) * (2 * Real.pi - x) - (L : ℝ) * (2 * Real.pi - y) =
            (L : ℝ) * (y - x) := by ring
        rw [heq, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg this,
          abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring_nf
        rfl
      · have hxb' : x ≤ sharp_b L := le_of_not_gt hxb
        simp [sharp_theta, hxb', hyb]
        calc
          |x / 2 - (L : ℝ) * (2 * Real.pi - y)| ≤
              |x / 2 - sharp_b L / 2| +
                |sharp_b L / 2 - (L : ℝ) * (2 * Real.pi - y)| :=
            abs_sub_le _ _ _
          _ = (sharp_b L / 2 - x / 2) +
              ((L : ℝ) * (y - sharp_b L)) := by
            have hfirst : x / 2 - sharp_b L / 2 ≤ 0 := by linarith
            have hyT : 2 * Real.pi - y ≤ sharp_a L := by
              dsimp [sharp_b] at hyb
              linarith
            have hsecond : 0 ≤ sharp_b L / 2 - (L : ℝ) * (2 * Real.pi - y) := by
              rw [hseam]
              nlinarith
            rw [abs_of_nonpos hfirst, abs_of_nonneg hsecond, hseam]
            ring_nf
            nlinarith [hsum]
          _ ≤ (L : ℝ) * (y - x) := by
            have hcoef : 0 ≤ (L : ℝ) + 1 / 2 := by linarith
            have hmul := mul_le_mul_of_nonneg_left hxb' hcoef
            nlinarith [hmul, hL]
          _ = (L : ℝ) * |x - y| := by
            rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
            ring
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hforward hx hy hxy
  · have h := hforward hy hx hyx
    simpa [dist_comm, abs_sub_comm] using h

private theorem addcircle_norm_coe_le_abs (z : ℝ) :
    ‖(z : AddCircle (2 * Real.pi))‖ ≤ |z| := by
  rw [QuotientAddGroup.norm_eq_infDist]
  have h := Metric.infDist_le_dist_of_mem (x := (0 : ℝ)) (y := z)
    (s := {r : ℝ | (r : AddCircle (2 * Real.pi)) = (z : AddCircle (2 * Real.pi))}) (by rfl)
  simpa [Real.dist_eq] using h

private theorem sharp_theta_circle_lipschitz
    (L : ℝ≥0) (hL : (1 / 2 : ℝ) ≤ (L : ℝ)) {u v : ℝ}
    (hu : u ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hv : v ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ ≤
      L * ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ := by
  have hT : 0 < (2 * Real.pi : ℝ) := by positivity
  have hTne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hT
  have hforward : ∀ {u v : ℝ}, u ∈ Ico (0 : ℝ) (2 * Real.pi) →
      v ∈ Ico (0 : ℝ) (2 * Real.pi) → u ≤ v →
      ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ ≤
        L * ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ := by
    intro u v hu hv huv
    have hucc : u ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hu.1, le_of_lt hu.2⟩
    have hvcc : v ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hv.1, le_of_lt hv.2⟩
    let d : ℝ := v - u
    have hd0 : 0 ≤ d := sub_nonneg.mpr huv
    have hraw : ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ ≤
        |sharp_theta L u - sharp_theta L v| := addcircle_norm_coe_le_abs _
    by_cases hdshort : d ≤ (2 * Real.pi) / 2
    · have hbase := (sharp_theta_lipschitzOn L hL).dist_le_mul u hucc v hvcc
      rw [Real.dist_eq, Real.dist_eq] at hbase
      have hinput : ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ = |u - v| :=
        (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (x := u - v) hTne).2 (by
          rw [abs_of_nonpos (sub_nonpos.mpr huv)]
          rw [abs_of_pos hT]
          simpa [d] using hdshort)
      calc
        ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ ≤
            |sharp_theta L u - sharp_theta L v| := hraw
        _ ≤ (L : ℝ) * |u - v| := by simpa [abs_sub_comm] using hbase
        _ = L * ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ := by rw [hinput]
    · have hdlong : (2 * Real.pi) / 2 < d := lt_of_not_ge hdshort
      have hcomp : 0 ≤ (2 * Real.pi) - d := by
        have := hv.2
        have := hu.1
        linarith
      have hcomp_le : (2 * Real.pi) - d ≤ (2 * Real.pi) / 2 := by linarith
      have hperiod : ((u - v : ℝ) : AddCircle (2 * Real.pi)) =
          (((u - v) + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) := by
        rw [AddCircle.coe_add]
        simp [AddCircle.coe_add]
      have hinput : ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ =
          (2 * Real.pi) - d := by
        rw [hperiod]
        have hnorm := (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi)
          (x := u - v + 2 * Real.pi) hTne).2 (by
            rw [abs_of_nonneg]
            · have heq : u - v + 2 * Real.pi = 2 * Real.pi - d := by
                dsimp [d]
                ring
              rw [heq]
              simpa [abs_of_pos hT] using hcomp_le
            · linarith [hu.1, hv.2])
        have heq : u - v + 2 * Real.pi = 2 * Real.pi - d := by
          dsimp [d]
          ring
        rw [hnorm, heq, abs_of_nonneg hcomp]
      by_cases hvb : v ≤ sharp_b L
      · have hub : u ≤ sharp_b L := huv.trans hvb
        have hbnd : d ≤ sharp_b L := by dsimp [d]; linarith [hu.1, hvb]
        have hmul := mul_le_mul_of_nonneg_left hcomp_le (by positivity : (0 : ℝ) ≤ (L : ℝ))
        have hseam : sharp_b L / 2 = (L : ℝ) * sharp_a L := by
          dsimp [sharp_b, sharp_a]
          field_simp
          ring
        have hsum : sharp_b L + sharp_a L = 2 * Real.pi := by
          dsimp [sharp_b]
          ring
        have hraw_bound : |sharp_theta L u - sharp_theta L v| ≤
            (L : ℝ) * ((2 * Real.pi) - d) := by
          simp only [sharp_theta, if_pos hub, if_pos hvb]
          rw [show u / 2 - v / 2 = (u - v) / 2 by ring, abs_div,
            abs_of_nonpos (sub_nonpos.mpr huv)]
          norm_num
          nlinarith [hL, hmul, hseam, hsum, hbnd]
        calc
          ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ ≤
              (L : ℝ) * ((2 * Real.pi) - d) := hraw.trans hraw_bound
          _ = L * ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ := by rw [hinput]
      · have hvb' : sharp_b L < v := lt_of_not_ge hvb
        by_cases hub : sharp_b L < u
        · have hlen : d ≤ sharp_a L := by
            have hlen' : d ≤ (2 * Real.pi) - sharp_b L := by
              dsimp [d]
              linarith [hv.2, hub]
            have heq : (2 * Real.pi) - sharp_b L = sharp_a L := by
              dsimp [sharp_b]
              ring
            rw [heq] at hlen'
            exact hlen'
          have ha_half : sharp_a L ≤ (2 * Real.pi) / 2 := by
            dsimp [sharp_a]
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) + 1)).2
            nlinarith [hL, Real.pi_pos]
          linarith
        · have hub' : u ≤ sharp_b L := le_of_not_gt hub
          have hseam : sharp_b L / 2 = (L : ℝ) * sharp_a L := by
            dsimp [sharp_b, sharp_a]
            field_simp
            ring
          have hsum : sharp_b L + sharp_a L = 2 * Real.pi := by
            dsimp [sharp_b]
            ring
          have hupper : |u / 2 - (L : ℝ) * (2 * Real.pi - v)| ≤
              (L : ℝ) * ((2 * Real.pi) - d) := by
            calc
              |u / 2 - (L : ℝ) * (2 * Real.pi - v)| ≤
                  |u / 2| + |(L : ℝ) * (2 * Real.pi - v)| := by
                    simpa [abs_sub_comm] using (abs_sub_le (u / 2) 0
                      ((L : ℝ) * (2 * Real.pi - v)))
              _ = u / 2 + (L : ℝ) * (2 * Real.pi - v) := by
                rw [abs_of_nonneg (by linarith [hu.1]), abs_mul,
                  abs_of_nonneg (by positivity), abs_of_nonneg (by linarith [hv.2])]
              _ ≤ (L : ℝ) * ((2 * Real.pi) - d) := by
                dsimp [d]
                nlinarith [hL, hu.1]
          have hraw' :
              ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ ≤
                |u / 2 - (L : ℝ) * (2 * Real.pi - v)| := by
            simpa only [sharp_theta, if_pos hub', if_neg (not_le_of_gt hvb')]
              using hraw
          calc
            ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ ≤
                (L : ℝ) * ((2 * Real.pi) - d) := hraw'.trans hupper
            _ = L * ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ := by rw [hinput]
  rcases le_total u v with huv | hvu
  · exact hforward hu hv huv
  · have h := hforward hv hu hvu
    have hleft :
        ((sharp_theta L v - sharp_theta L u : ℝ) : AddCircle (2 * Real.pi)) =
          -((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi)) := by
      rw [← AddCircle.coe_neg]
      congr 1 <;> ring
    have hright :
        ((v - u : ℝ) : AddCircle (2 * Real.pi)) =
          -((u - v : ℝ) : AddCircle (2 * Real.pi)) := by
      rw [← AddCircle.coe_neg]
      congr 1 <;> ring
    calc
      ‖((sharp_theta L u - sharp_theta L v : ℝ) : AddCircle (2 * Real.pi))‖ =
          ‖((sharp_theta L v - sharp_theta L u : ℝ) : AddCircle (2 * Real.pi))‖ := by
            rw [hleft, norm_neg]
      _ ≤ L * ‖((v - u : ℝ) : AddCircle (2 * Real.pi))‖ := h
      _ = L * ‖((u - v : ℝ) : AddCircle (2 * Real.pi))‖ := by
        rw [hright, norm_neg]

private theorem sharp_map_lipschitz [Fact (0 < (2 * Real.pi : ℝ))]
    (L : ℝ≥0) (hL : (1 / 2 : ℝ) ≤ (L : ℝ)) :
    LipschitzWith L (sharp_map L) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  obtain ⟨u, hu, rfl⟩ := AddCircle.eq_coe_Ico x
  obtain ⟨v, hv, rfl⟩ := AddCircle.eq_coe_Ico y
  rw [sharp_map, AddCircle.liftIco_zero_coe_apply hu,
    AddCircle.liftIco_zero_coe_apply hv]
  rw [dist_eq_norm, ← AddCircle.coe_sub, dist_eq_norm, ← AddCircle.coe_sub]
  exact sharp_theta_circle_lipschitz L hL hu hv

private theorem sharp_weight_interval_integral
    (L : ℝ≥0) (hL : (1 / 2 : ℝ) ≤ (L : ℝ)) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), weight (2 * sharp_theta L t - t)) =
      4 * Real.pi / (2 * (L : ℝ) + 1) := by
  let T : ℝ := 2 * Real.pi
  let a : ℝ := sharp_a L
  let b : ℝ := sharp_b L
  let c : ℝ := -(2 * (L : ℝ) + 1)
  let d : ℝ := 2 * (L : ℝ) * T
  have hden : 0 < 2 * (L : ℝ) + 1 := by positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have ha : 0 < a := by dsimp [a, sharp_a, T]; positivity
  have haT : a ≤ T := by
    dsimp [a, T, sharp_a]
    apply (div_le_iff₀ hden).2
    nlinarith [Real.pi_pos]
  have hb0 : 0 ≤ b := by dsimp [b, sharp_b, T] at *; linarith
  have hbT : b ≤ T := by dsimp [b, sharp_b, T]; linarith
  have hc : c ≠ 0 := neg_ne_zero.mpr (ne_of_gt hden)
  have hcb : c * b + d = 0 := by
    dsimp [c, b, d, T, sharp_b, sharp_a]
    field_simp [ne_of_gt hden]
    ring
  have hcT : c * T + d = -T := by dsimp [c, d]; ring
  have hweightcont : Continuous weight := by unfold weight; fun_prop
  have htheta : ContinuousOn (sharp_theta L) (Icc 0 T) := by
    simpa [T] using (sharp_theta_lipschitzOn L hL).continuousOn
  have hphasecont : ContinuousOn (fun t => 2 * sharp_theta L t - t) (Icc 0 T) :=
    (continuousOn_const.mul htheta).sub continuous_id.continuousOn
  have hW : ContinuousOn (fun t => weight (2 * sharp_theta L t - t)) (Icc 0 T) :=
    (hweightcont.continuousOn : ContinuousOn weight univ).comp hphasecont
      (fun _ _ => mem_univ _)
  have h0b : IntervalIntegrable (fun t => weight (2 * sharp_theta L t - t)) volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb0]
    exact hW.mono (fun _ ht => ⟨ht.1, ht.2.trans hbT⟩)
  have hbTInt : IntervalIntegrable (fun t => weight (2 * sharp_theta L t - t)) volume b T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hbT]
    exact hW.mono (fun _ ht => ⟨hb0.trans ht.1, ht.2⟩)
  have hfirst : (∫ t in (0 : ℝ)..b, weight (2 * sharp_theta L t - t)) = 0 := by
    have heq : EqOn (fun t => weight (2 * sharp_theta L t - t)) (fun _ => (0 : ℝ))
        (uIcc 0 b) := by
      intro t ht
      have htb : t ≤ b := (show t ∈ Icc 0 b by simpa [uIcc_of_le hb0] using ht).2
      simp only [sharp_theta, if_pos (show t ≤ sharp_b L from htb)]
      have hzero : 2 * (t / 2) - t = 0 := by ring
      simp [hzero, weight]
    rw [intervalIntegral.integral_congr heq]
    simp
  have hphase (t : ℝ) (hbt : b ≤ t) :
      2 * sharp_theta L t - t = c * t + d := by
    by_cases htb : t ≤ b
    · have ht : t = b := le_antisymm htb hbt
      subst t
      simp only [sharp_theta, if_pos (show b ≤ sharp_b L from le_rfl)]
      rw [hcb]
      ring
    · simp only [sharp_theta, if_neg (show ¬t ≤ sharp_b L from htb)]
      dsimp [c, d, T]
      ring
  have hsecond : (∫ t in b..T, weight (2 * sharp_theta L t - t)) =
      4 * Real.pi / (2 * (L : ℝ) + 1) := by
    have heq : EqOn (fun t => weight (2 * sharp_theta L t - t))
        (fun t => weight (c * t + d)) (uIcc b T) := by
      intro t ht
      have hbt : b ≤ t := (show t ∈ Icc b T by simpa [uIcc_of_le hbT] using ht).1
      change weight (2 * sharp_theta L t - t) = weight (c * t + d)
      rw [hphase t hbt]
    rw [intervalIntegral.integral_congr heq]
    rw [intervalIntegral.integral_comp_mul_add weight hc d, smul_eq_mul, hcb, hcT]
    have hweightint : (∫ x in (0 : ℝ)..(-T), weight x) = -(4 * Real.pi) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => primitive_hasDerivAt x) (hweightcont.intervalIntegrable _ _)]
      dsimp [primitive, T]
      simp [Real.sin_neg, Real.sin_two_pi]
      ring
    rw [hweightint]
    change (-(2 * (L : ℝ) + 1))⁻¹ * (-(4 * Real.pi)) =
      4 * Real.pi / (2 * (L : ℝ) + 1)
    rw [inv_neg]
    ring
  change (∫ t in (0 : ℝ)..T, weight (2 * sharp_theta L t - t)) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals h0b hbTInt, hfirst, zero_add,
    hsecond]

private theorem sharp_map_error [Fact (0 < (2 * Real.pi : ℝ))]
    (L : ℝ≥0) (hL : (1 / 2 : ℝ) ≤ (L : ℝ)) :
    (∫ x : AddCircle (2 * Real.pi), circle_error (sharp_map L) x
      ∂AddCircle.haarAddCircle) = 2 / (2 * (L : ℝ) + 1) := by
  have hperiod : 0 < (2 * Real.pi : ℝ) := by positivity
  have hden : 0 < 2 * (L : ℝ) + 1 := by positivity
  have hinter :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        circle_error (sharp_map L) (t : AddCircle (2 * Real.pi))) =
      4 * Real.pi / (2 * (L : ℝ) + 1) := by
    calc
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        circle_error (sharp_map L) (t : AddCircle (2 * Real.pi))) =
          ∫ t in (0 : ℝ)..(2 * Real.pi), weight (2 * sharp_theta L t - t) := by
            apply intervalIntegral.integral_congr_Ioo_of_le hperiod.le
            intro t ht
            have htico : t ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨ht.1.le, ht.2⟩
            have hproj : (sharp_theta L t : AddCircle (2 * Real.pi)) =
                sharp_map L (t : AddCircle (2 * Real.pi)) := by
              simp [sharp_map, AddCircle.liftIco_zero_coe_apply htico]
            exact circle_error_on_lift (sharp_map L) (sharp_theta L t) t hproj
      _ = 4 * Real.pi / (2 * (L : ℝ) + 1) := sharp_weight_interval_integral L hL
  have hpre := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 (circle_error (sharp_map L))
  have hhaar := AddCircle.integral_haarAddCircle (f := circle_error (sharp_map L))
  rw [hhaar, smul_eq_mul, ← hpre]
  simp only [zero_add]
  rw [hinter]
  field_simp [Real.pi_ne_zero, ne_of_gt hden]
  ring

/- The metric in the hypothesis is the intrinsic quotient metric on `AddCircle`;
   only the reconstruction error is measured by the complex chord. -/
/-- Every intrinsically `L`-Lipschitz selector has the sharp uniform mean error bound. -/
theorem lower_bound (L : ℝ≥0)
    (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi))
    (hs : LipschitzWith L s) :
    2 / (2 * (L : ℝ) + 1) ≤
      ∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩
  exact circle_lipschitz_error_lower_bound L s hs

/-- For `L ≥ 1/2`, a circle map attains the lower bound with intrinsic Lipschitz constant `L`. -/
theorem sharpness (L : ℝ≥0) (hL : (1 / 2 : ℝ) ≤ (L : ℝ)) :
    ∃ s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi),
      LipschitzWith L s ∧
      (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle) =
        2 / (2 * (L : ℝ) + 1) := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩
  exact ⟨sharp_map L, sharp_map_lipschitz L hL, sharp_map_error L hL⟩

#print axioms lower_bound
#print axioms sharpness

end
end D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
