/- GID: D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity
   mirror-E: none(waiver:abstract-spectral-calculus)
   anchors: []
   utility: none
   digest: Increasing finite positive exponents enlarges finite-spectrum quantum cost cones. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import D5.S3.Analytic.Convexity.MeasurableFiniteMoments
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
The finite-spectrum form of equations (21), (22), and (27) of Bunth,
Pitrik, Titkos, and Virosztek, arXiv:2501.08066v3, uses algebraic tensor
costs before transposition of the second factor, on arbitrary complex
Hilbert spaces without dimension or separability restrictions.

admission_basis: open-problem-resolution
Preregistration: issue #30813, Conjecture 9, arXiv:2501.08066v3.
proof_shape: bind-only for every theorem, including result.
All auxiliary statements lie on the live derivation path to result.
The positive sine mixture, norm-density reduction to finite moments,
and spectral lift are compositions of existing results, not escape witnesses.
The direct frozen prerequisite is MeasurableFiniteMoments.finite_moments.
No computational-content category applies: all assertions quantify arbitrary spectra.
-/

section SineIntegralHelpers
noncomputable section
open Set MeasureTheory Real

namespace D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

/-- The scalar kernel in the classical sine representation of snowflake distances. -/
def sineKernel (p q u : ℝ) : ℝ := |sin u| ^ q * u ^ (-1 - p)

/-- The positive normalizing sine moment. -/
def sineMoment (p q : ℝ) : ℝ := ∫ u in Ioi 0, sineKernel p q u

/-- The phase average of the absolute cosine power. -/
def phaseMoment (q : ℝ) : ℝ := ∫ θ in 0..2 * π, |cos θ| ^ q

private lemma continuousOn_sineKernel {q : ℝ} (hq : 0 < q) (p : ℝ) :
    ContinuousOn (sineKernel p q) (Ioi 0) := by
  unfold sineKernel
  apply ContinuousOn.mul
  · exact (continuous_abs.comp continuous_sin).rpow_const (fun _ => Or.inr hq.le) |>.continuousOn
  · exact continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt hu))

private lemma sineKernel_nonneg (p q u : ℝ) (hu : 0 ≤ u) : 0 ≤ sineKernel p q u := by
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hu _)

/-- The sine moment converges precisely in the range needed for exponent monotonicity. -/
private theorem integrableOn_sineKernel {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    IntegrableOn (sineKernel p q) (Ioi 0) := by
  have hq : 0 < q := hp.trans hpq
  have hsmall : IntegrableOn (sineKernel p q) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    refine Integrable.mono' ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by linarith : -1 < q - 1 - p))
      (((continuousOn_sineKernel hq p).mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo)
      ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
    rw [Real.norm_of_nonneg (sineKernel_nonneg p q u hu.1.le)]
    unfold sineKernel
    calc
      |sin u| ^ q * u ^ (-1 - p) ≤ u ^ q * u ^ (-1 - p) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu.1.le _)
        exact Real.rpow_le_rpow (abs_nonneg _) (by simpa [abs_of_pos hu.1] using
          (Real.abs_sin_le_abs (x := u))) hq.le
      _ = u ^ (q - 1 - p) := by
        rw [← Real.rpow_add hu.1]
        congr 1
        ring
  have hlarge : IntegrableOn (sineKernel p q) (Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - p < -1)
      zero_lt_one) (((continuousOn_sineKernel hq p).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    rw [Real.norm_of_nonneg (sineKernel_nonneg p q u (le_of_lt (zero_lt_one.trans hu)))]
    unfold sineKernel
    have hpow : |sin u| ^ q ≤ 1 := by
      simpa using Real.rpow_le_rpow (abs_nonneg (sin u)) (abs_sin_le_one u) hq.le
    exact mul_le_of_le_one_left (Real.rpow_nonneg (le_of_lt (zero_lt_one.trans hu)) _) hpow
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hsmall.union hlarge

/-- The normalizing sine moment is strictly positive. -/
theorem sineMoment_pos {p q : ℝ} (hp : 0 < p) (hpq : p < q) : 0 < sineMoment p q := by
  unfold sineMoment
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => sineKernel_nonneg p q u hu.le)
    (integrableOn_sineKernel hp hpq)).2
  apply (show 0 < volume (Ioo 0 π) by simp [Real.pi_pos]).trans_le
  apply measure_mono
  intro u hu
  refine ⟨?_, hu.1⟩
  apply Function.mem_support.mpr
  exact (mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (sin_pos_of_mem_Ioo hu).ne') _)
    (Real.rpow_pos_of_pos hu.1 _)).ne'

private lemma continuous_cos_rpow {q : ℝ} (hq : 0 < q) :
    Continuous (fun θ : ℝ => |cos θ| ^ q) :=
  (continuous_abs.comp continuous_cos).rpow_const (fun _ => Or.inr hq.le)

/-- The phase average is strictly positive. -/
theorem phaseMoment_pos {q : ℝ} (hq : 0 < q) : 0 < phaseMoment q := by
  unfold phaseMoment
  apply intervalIntegral.integral_pos
    (by positivity : (0 : ℝ) < 2 * π) (continuous_cos_rpow hq).continuousOn
  · intro u hu
    exact Real.rpow_nonneg (abs_nonneg _) _
  · exact ⟨0, by constructor <;> positivity, by simp⟩

/-- Averaging over a full phase period separates the difference and midpoint variables. -/
private theorem phase_distance_integral (q a b : ℝ) :
    (∫ θ in 0..2 * π, |sin (a + θ) - sin (b + θ)| ^ q) =
      2 ^ q * |sin ((a - b) / 2)| ^ q * phaseMoment q := by
  have hfactor (θ : ℝ) :
      |sin (a + θ) - sin (b + θ)| ^ q =
        (2 ^ q * |sin ((a - b) / 2)| ^ q) * |cos (θ + (a + b) / 2)| ^ q := by
    rw [sin_sub_sin]
    have hs : (a + θ - (b + θ)) / 2 = (a - b) / 2 := by ring
    have hc : (a + θ + (b + θ)) / 2 = θ + (a + b) / 2 := by ring
    rw [hs, hc, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.mul_rpow (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)]
  simp_rw [hfactor]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right
    (fun θ : ℝ => |cos θ| ^ q) ((a+b)/2)]
  have hperiod : Function.Periodic (fun θ : ℝ => |cos θ| ^ q) (2 * π) :=
    cos_periodic.comp (fun x : ℝ => |x| ^ q)
  have heq := hperiod.intervalIntegral_add_eq ((a + b) / 2) 0
  simp only [zero_add] at heq ⊢
  rw [show 2 * π + (a + b) / 2 = (a + b) / 2 + 2 * π by ring, heq]
  rfl

private lemma scaled_sineKernel {c : ℝ} (hc : 0 < c) (p q : ℝ) {t : ℝ}
    (ht : 0 < t) :
    |sin (c * t)| ^ q * t ^ (-1 - p) =
      c ^ (1 + p) * sineKernel p q (c * t) := by
  unfold sineKernel
  rw [Real.mul_rpow hc.le ht.le]
  have hcancel : c ^ (1 + p) * c ^ (-1 - p) = 1 := by
    rw [← Real.rpow_add hc]
    rw [show (1+p)+(-1-p) = 0 by ring, Real.rpow_zero]
  calc
    _ = (c ^ (1+p) * c ^ (-1-p)) * (|sin (c*t)| ^ q * t ^ (-1-p)) := by
      rw [hcancel]
      ring
    _ = _ := by ring

private lemma sine_scale_factor {c : ℝ} (hc : 0 < c) (p : ℝ) :
    c ^ (1 + p) * c⁻¹ = c ^ p := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 1
  ring

/-- Positive dilation extracts the expected homogeneous power from the sine moment. -/
private theorem sine_integral_scale {c : ℝ} (hc : 0 < c) (p q : ℝ) :
    (∫ t in Ioi 0, |sin (c * t)| ^ q * t ^ (-1 - p)) = c ^ p * sineMoment p q := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => scaled_sineKernel hc p q ht), integral_const_mul,
    integral_comp_mul_left_Ioi (sineKernel p q) 0 hc]
  simp only [mul_zero, smul_eq_mul]
  rw [← mul_assoc, sine_scale_factor hc]
  rfl

/-- The dilated sine kernel remains integrable. -/
private theorem integrableOn_sine_scale {p q c : ℝ} (hp : 0 < p) (hpq : p < q) (hc : 0 < c) :
    IntegrableOn (fun t => |sin (c * t)| ^ q * t ^ (-1 - p)) (Ioi 0) := by
  have hi : IntegrableOn (fun t => sineKernel p q (c * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (sineKernel p q) 0 hc).2
    simpa using integrableOn_sineKernel hp hpq
  exact IntegrableOn.congr_fun (hi.const_mul (c ^ (1+p)))
    (fun t ht => (scaled_sineKernel hc p q ht).symm) measurableSet_Ioi

private lemma abs_sine_distance (t x y : ℝ) :
    |sin (t * (x - y) / 2)| = |sin ((|x - y| / 2) * t)| := by
  rcases le_total 0 (x - y) with h | h
  · rw [abs_of_nonneg h]
    congr 2
    ring
  · rw [abs_of_nonpos h]
    have heq : t * (x - y) / 2 = -((- (x - y) / 2) * t) := by ring
    rw [heq, sin_neg, abs_neg]

/-- The phase-averaged sine representation of a positive real distance power. -/
private theorem sine_distance_representation {p q : ℝ} (hp : 0 < p) (hpq : p < q) (x y : ℝ) :
    (∫ t in Ioi 0, (∫ θ in 0..2 * π,
      |sin (t * x + θ) - sin (t * y + θ)| ^ q) * t ^ (-1 - p)) =
        (2 ^ q * phaseMoment q * sineMoment p q / 2 ^ p) * |x - y| ^ p := by
  have hq : 0 < q := hp.trans hpq
  simp_rw [phase_distance_integral]
  by_cases hxy : x = y
  · subst y
    simp [Real.zero_rpow hq.ne', Real.zero_rpow hp.ne']
  have hd : 0 < |x - y| / 2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hxy)) two_pos
  have hrewrite (t : ℝ) :
      2 ^ q * |sin ((t * x - t * y) / 2)| ^ q * phaseMoment q * t ^ (-1 - p) =
      (2 ^ q * phaseMoment q) * (|sin ((|x-y|/2) * t)| ^ q * t ^ (-1-p)) := by
    rw [show (t * x - t * y) / 2 = t * (x - y) / 2 by ring,
      abs_sine_distance]
    ring
  simp_rw [hrewrite]
  rw [integral_const_mul, sine_integral_scale hd, Real.div_rpow (abs_nonneg _) (by norm_num)]
  unfold sineMoment
  ring

/-- Integrability of the phase-averaged sine representation. -/
private theorem integrableOn_sine_distance {p q : ℝ} (hp : 0 < p) (hpq : p < q) (x y : ℝ) :
    IntegrableOn (fun t => (∫ θ in 0..2 * π,
      |sin (t * x + θ) - sin (t * y + θ)| ^ q) * t ^ (-1 - p)) (Ioi 0) := by
  have hq : 0 < q := hp.trans hpq
  by_cases hxy : x = y
  · subst y
    simpa [Real.zero_rpow hq.ne'] using
      (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0))
  have hd : 0 < |x-y| / 2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hxy)) two_pos
  refine IntegrableOn.congr_fun
    ((integrableOn_sine_scale hp hpq hd).const_mul (2 ^ q * phaseMoment q))
    (fun t ht => ?_) measurableSet_Ioi
  rw [phase_distance_integral]
  rw [show (t * x - t * y) / 2 = t * (x-y) / 2 by ring, abs_sine_distance]
  ring

/-- The product measure for the positive dilation and uniform phase parameters. -/
def sineParameterMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 (2 * π)))

/-- A weighted coordinate distance in the sine embedding. -/
def sineDistanceIntegrand (p q x y : ℝ) (a : ℝ × ℝ) : ℝ :=
  |sin (a.1 * x + a.2) - sin (a.1 * y + a.2)| ^ q * a.1 ^ (-1-p)

/-- The sine representation is an actual integrable positive mixture. -/
theorem integrable_sineDistance {p q : ℝ} (hp : 0 < p) (hpq : p < q) (x y : ℝ) :
    Integrable (sineDistanceIntegrand p q x y) sineParameterMeasure := by
  have hq : 0 < q := hp.trans hpq
  have hphase (t : ℝ) : IntervalIntegrable
      (fun θ => |sin (t*x+θ) - sin (t*y+θ)| ^ q) volume 0 (2*π) := by
    apply Continuous.intervalIntegrable
    apply Continuous.rpow_const _ (fun _ => Or.inr hq.le)
    fun_prop
  unfold sineParameterMeasure
  apply (integrable_prod_iff (show AEStronglyMeasurable (sineDistanceIntegrand p q x y)
    ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 (2*π)))) from by
      apply Measurable.aestronglyMeasurable
      unfold sineDistanceIntegrand
      fun_prop)).2
  constructor
  · filter_upwards with t
    change Integrable (fun θ : ℝ =>
      |sin (t*x+θ) - sin (t*y+θ)| ^ q * t ^ (-1-p)) _
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0:ℝ) ≤ 2*π)).1
      (hphase t)).mul_const (t ^ (-1-p))
  · refine (integrableOn_sine_distance hp hpq x y).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    symm
    change (∫ θ in Ioc 0 (2*π), ‖sineDistanceIntegrand p q x y (t,θ)‖) = _
    have hnorm (θ : ℝ) : ‖sineDistanceIntegrand p q x y (t,θ)‖ =
        |sin (t*x+θ) - sin (t*y+θ)| ^ q * t^(-1-p) := by
      unfold sineDistanceIntegrand
      exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg ht.le _))
    simp_rw [hnorm]
    rw [integral_mul_const, ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*π)]

/-- The product-measure form of the classical sine distance representation. -/
theorem integral_sineDistance {p q : ℝ} (hp : 0 < p) (hpq : p < q) (x y : ℝ) :
    (∫ a, sineDistanceIntegrand p q x y a ∂sineParameterMeasure) =
      (2 ^ q * phaseMoment q * sineMoment p q / 2 ^ p) * |x-y|^p := by
  rw [sineParameterMeasure, integral_prod _ (integrable_sineDistance hp hpq x y)]
  unfold sineDistanceIntegrand
  simp_rw [integral_mul_const,
    ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*π)]
  exact sine_distance_representation hp hpq x y

end D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

end
end SineIntegralHelpers

section FiniteDecompositionHelpers
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

/-- Positive conic cubature for an integrable finite-dimensional map on an
arbitrary measure space. The finite measure used for cubature has density the
norm of the map. -/
theorem finite_conic_moments {E α : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace α]
    (μ : Measure α) {f : α → E} (hfm : StronglyMeasurable f) (hfi : Integrable f μ)
    {s : Set α} (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (a : Fin k → α),
      (∀ i, 0 ≤ w i) ∧ (∀ i, a i ∈ s) ∧
      ∑ i, w i • f (a i) = ∫ a, f a ∂μ := by
  classical
  let ρ : α → ℝ≥0 := fun a => ‖f a‖₊
  have hρm : Measurable ρ := hfm.nnnorm.measurable
  let ν : Measure α := μ.withDensity fun a => (ρ a : ℝ≥0∞)
  haveI : IsFiniteMeasure ν := by
    have h := isFiniteMeasure_withDensity_ofReal hfi.norm.hasFiniteIntegral
    simpa only [ν, ρ, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal] using h
  let g : α → E := fun a => ‖f a‖⁻¹ • f a
  have hcancel : (fun a => (ρ a : ℝ) • g a) = f := by
    funext a
    by_cases hfa : f a = 0
    · simp [g, hfa, ρ]
    · simp [g, ρ, smul_smul, norm_ne_zero_iff.mpr hfa]
  have hgi : Integrable g ν := by
    apply (integrable_withDensity_iff_integrable_coe_smul hρm).mpr
    rwa [hcancel]
  have hsν : ∀ᵐ a ∂ν, a ∈ s :=
    hs.filter_mono (Measure.ae_mono' (withDensity_absolutelyContinuous μ _))
  obtain ⟨k, w, a, hw, _, ha, he⟩ :=
    D5.S3.Analytic.Convexity.MeasurableFiniteMoments.finite_moments ν hgi hsν
  refine ⟨k, fun i => w i * ‖f (a i)‖⁻¹, a,
    fun i => mul_nonneg (hw i) (inv_nonneg.mpr (norm_nonneg _)), ha, ?_⟩
  calc
    ∑ i, (w i * ‖f (a i)‖⁻¹) • f (a i) = ∑ i, w i • g (a i) := by
      simp only [g, smul_smul]
    _ = ∫ a, g a ∂ν := he
    _ = ∫ a, (ρ a : ℝ) • g a ∂μ :=
      integral_withDensity_eq_integral_smul hρm g
    _ = ∫ a, f a ∂μ := by rw [hcancel]

/-- The vector of all ordered-pair q-distances on a finite configuration. -/
def distanceVector {I : Type*} (q : ℝ) (z : I → ℝ) : I × I → ℝ :=
  fun ij => |z ij.1 - z ij.2| ^ q

private theorem distanceVector_root_scale {I : Type*} (q : ℝ) (hq : q ≠ 0)
    (z : I → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    distanceVector q (fun i => c ^ q⁻¹ * z i) = c • distanceVector q z := by
  funext ij
  change |c ^ q⁻¹ * z ij.1 - c ^ q⁻¹ * z ij.2| ^ q =
    c * |z ij.1 - z ij.2| ^ q
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg hc _),
    Real.mul_rpow (Real.rpow_nonneg hc _) (abs_nonneg _), Real.rpow_inv_rpow hc hq]

/-- A positive integral representation of pair distances on a finite set admits
an exact finite sum of q-distances, with all coefficients absorbed into the
new configurations. -/
theorem finite_distance_decomposition_of_integral {I α : Type*} [Fintype I]
    [MeasurableSpace α] (μ : Measure α) (p q : ℝ) (hq : 0 < q)
    (lam : I → ℝ) (z : α → I → ℝ) (r : α → ℝ) (hr : ∀ᵐ a ∂μ, 0 ≤ r a)
    (hfm : StronglyMeasurable (fun a => r a • distanceVector q (z a)))
    (hfi : Integrable (fun a => r a • distanceVector q (z a)) μ)
    (hmoment : (∫ a, r a • distanceVector q (z a) ∂μ) = distanceVector p lam) :
    ∃ (k : ℕ) (v : Fin k → I → ℝ),
      ∀ i j, |lam i - lam j| ^ p = ∑ l, |v l i - v l j| ^ q := by
  classical
  obtain ⟨k, w, a, hw, ha, he⟩ := finite_conic_moments μ hfm hfi hr
  let v : Fin k → I → ℝ := fun l i => (w l * r (a l)) ^ q⁻¹ * z (a l) i
  have hvector : (∑ l, distanceVector q (v l)) = distanceVector p lam := by
    calc
      (∑ l, distanceVector q (v l)) =
          ∑ l, (w l * r (a l)) • distanceVector q (z (a l)) := by
        apply Finset.sum_congr rfl
        intro l _
        exact distanceVector_root_scale q hq.ne' (z (a l)) (w l * r (a l))
          (mul_nonneg (hw l) (ha l))
      _ = ∑ l, w l • (r (a l) • distanceVector q (z (a l))) := by
        simp only [smul_smul]
      _ = distanceVector p lam := he.trans hmoment
  refine ⟨k, v, fun i j => ?_⟩
  simpa only [distanceVector, Finset.sum_apply] using
    (congrFun hvector (i, j)).symm

/-- Finite exact decomposition of a lower positive power of real pair distances
as a finite sum of distances of any larger positive power. -/
theorem finite_distance_decomposition {I : Type*} [Fintype I]
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (lam : I → ℝ) :
    ∃ (k : ℕ) (v : Fin k → I → ℝ),
      ∀ i j, |lam i - lam j| ^ p = ∑ l, |v l i - v l j| ^ q := by
  classical
  have hq : 0 < q := hp.trans hpq
  let c : ℝ := 2 ^ q * phaseMoment q * sineMoment p q / 2 ^ p
  have hc : 0 < c := by
    have hs := sineMoment_pos hp hpq
    have hθ := phaseMoment_pos hq
    dsimp [c]
    positivity
  let z : ℝ × ℝ → I → ℝ := fun a i => Real.sin (a.1 * lam i + a.2)
  let r : ℝ × ℝ → ℝ := fun a => a.1 ^ (-1-p) / c
  let F : ℝ × ℝ → I × I → ℝ := fun a ij =>
    sineDistanceIntegrand p q (lam ij.1) (lam ij.2) a / c
  have hFm : StronglyMeasurable F := by
    apply Measurable.stronglyMeasurable
    apply Measurable.of_eval
    intro ij
    unfold F sineDistanceIntegrand
    fun_prop
  have hFi : Integrable F sineParameterMeasure := by
    apply Integrable.of_eval
    intro ij
    exact (integrable_sineDistance hp hpq (lam ij.1) (lam ij.2)).div_const c
  have hmoment : (∫ a, F a ∂sineParameterMeasure) = distanceVector p lam := by
    apply funext
    intro ij
    rw [eval_integral (f := F) (fun ij => hFi.eval ij) ij]
    change (∫ a, sineDistanceIntegrand p q (lam ij.1) (lam ij.2) a / c
      ∂sineParameterMeasure) = |lam ij.1 - lam ij.2| ^ p
    rw [integral_div, integral_sineDistance hp hpq]
    change (c * |lam ij.1 - lam ij.2| ^ p) / c = _
    field_simp [hc.ne']
  have hr : ∀ᵐ a ∂sineParameterMeasure, 0 ≤ r a := by
    unfold sineParameterMeasure
    rw [Measure.ae_prod_iff_ae_ae (show MeasurableSet {a : ℝ × ℝ | 0 ≤ r a} from by
      apply measurableSet_le measurable_const
      unfold r
      fun_prop)]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Filter.Eventually.of_forall fun θ =>
      div_nonneg (Real.rpow_nonneg ht.le _) hc.le
  have hf_eq : (fun a => r a • distanceVector q (z a)) = F := by
    ext a ij
    simp only [r, z, distanceVector, F, sineDistanceIntegrand, Pi.smul_apply, smul_eq_mul]
    ring
  apply finite_distance_decomposition_of_integral sineParameterMeasure p q hq lam z r hr
  · rw [hf_eq]
    exact hFm
  · rw [hf_eq]
    exact hFi
  · rw [hf_eq]
    exact hmoment

#print axioms finite_conic_moments
#print axioms finite_distance_decomposition_of_integral
#print axioms finite_distance_decomposition

end D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

end
end FiniteDecompositionHelpers

section MonotonicityHelpers
noncomputable section
open Set
open scoped BigOperators TensorProduct Classical

namespace D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded selfadjoint observable with finite real spectrum. -/
def IsFiniteObservable (A : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint A ∧ (spectrum ℝ A).Finite

/-- The spectral projection at a specified real value. -/
def specProj (A : H →L[ℂ] H) (x : ℝ) : H →L[ℂ] H :=
  cfc (fun t : ℝ => if t = x then (1 : ℝ) else 0) A

/-- The algebraic tensor cost; the irrelevant infinite-spectrum branch is zero. -/
def costElem (p : ℝ) (A : H →L[ℂ] H) :
    (H →L[ℂ] H) ⊗[ℂ] (H →L[ℂ] H) :=
  if h : (spectrum ℝ A).Finite then
    ∑ x ∈ h.toFinset, ∑ y ∈ h.toFinset,
      |x - y| ^ p • (specProj A x ⊗ₜ[ℂ] specProj A y)
  else 0

/-- Finite sums of costs of finite-spectrum selfadjoint observables. -/
def costCone (p : ℝ) : Set ((H →L[ℂ] H) ⊗[ℂ] (H →L[ℂ] H)) :=
  {C | ∃ L : List (H →L[ℂ] H), (∀ A ∈ L, IsFiniteObservable A) ∧
    C = (L.map (costElem p)).sum}

theorem finiteObservable_cfc {A : H →L[ℂ] H}
    (hA : IsFiniteObservable A) (f : ℝ → ℝ) : IsFiniteObservable (cfc f A) := by
  refine ⟨IsSelfAdjoint.cfc, ?_⟩
  rw [cfc_map_spectrum f A hA.1 (hA.2.continuousOn f)]
  exact hA.2.image f

/-- The spectral projections of a function of an observable are the sums over its fibers. -/
theorem specProj_cfc {A : H →L[ℂ] H} (hA : IsFiniteObservable A)
    (f : ℝ → ℝ) (v : ℝ) :
    specProj (cfc f A) v =
      ∑ x ∈ hA.2.toFinset.filter (fun x => f x = v), specProj A x := by
  classical
  let s := hA.2.toFinset.filter (fun x => f x = v)
  rw [specProj, ← cfc_comp (fun t : ℝ => if t = v then (1 : ℝ) else 0) f A
    hA.1 ((hA.2.image f).continuousOn _) (hA.2.continuousOn f)]
  calc
    _ = cfc (∑ x ∈ s, fun t : ℝ => if t = x then (1 : ℝ) else 0) A := by
      apply cfc_congr
      intro t ht
      have ht' : t ∈ hA.2.toFinset := hA.2.mem_toFinset.mpr ht
      simp [s, Function.comp_def, ht', Finset.sum_apply]
    _ = _ := cfc_sum _ A s (fun _ _ => hA.2.continuousOn _)

/-- Exact regrouping of a tensor-valued double sum along finite fibers. -/
private theorem tensor_fiber_sum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Finset ℝ) (f : ℝ → ℝ) (P : ℝ → V) (w : ℝ → ℝ → ℝ) :
    (∑ v ∈ s.image f, ∑ z ∈ s.image f,
      w v z • ((∑ i ∈ s.filter (fun i => f i = v), P i) ⊗ₜ[ℂ]
        (∑ j ∈ s.filter (fun j => f j = z), P j))) =
      ∑ i ∈ s, ∑ j ∈ s, w (f i) (f j) • (P i ⊗ₜ[ℂ] P j) := by
  classical
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, Finset.smul_sum]
  calc
    _ = ∑ v ∈ s.image f, ∑ i ∈ s.filter (fun i => f i = v),
        ∑ z ∈ s.image f, ∑ j ∈ s.filter (fun j => f j = z),
          w (f i) (f j) • (P i ⊗ₜ[ℂ] P j) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
    _ = _ := by
      simp_rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi)]

/-- Functional calculus transports costs by evaluating the new labels on the old spectrum. -/
theorem costElem_cfc {A : H →L[ℂ] H} (hA : IsFiniteObservable A)
    (q : ℝ) (f : ℝ → ℝ) :
    costElem q (cfc f A) = ∑ x ∈ hA.2.toFinset, ∑ y ∈ hA.2.toFinset,
      |f x - f y| ^ q • (specProj A x ⊗ₜ[ℂ] specProj A y) := by
  classical
  have hB := finiteObservable_cfc hA f
  have hs : hB.2.toFinset = hA.2.toFinset.image f := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_image]
    rw [cfc_map_spectrum f A hA.1 (hA.2.continuousOn f)]
    rfl
  rw [costElem, dif_pos hB.2, hs]
  simp_rw [specProj_cfc hA f]
  exact tensor_fiber_sum _ _ _ _

/-- A scalar decomposition lifts to an equality of finite-spectrum operator costs. -/
theorem costElem_of_decomposition {A : H →L[ℂ] H}
    (hA : IsFiniteObservable A) (p q : ℝ) {k : ℕ} (f : Fin k → ℝ → ℝ)
    (h : ∀ x ∈ hA.2.toFinset, ∀ y ∈ hA.2.toFinset,
      |x - y| ^ p = ∑ l, |f l x - f l y| ^ q) :
    costElem p A = ∑ l, costElem q (cfc (f l) A) := by
  classical
  calc
    costElem p A = ∑ x ∈ hA.2.toFinset, ∑ y ∈ hA.2.toFinset,
        ∑ l, |f l x - f l y| ^ q • (specProj A x ⊗ₜ[ℂ] specProj A y) := by
      rw [costElem, dif_pos hA.2]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [h x hx y hy, Finset.sum_smul]
    _ = ∑ l, ∑ x ∈ hA.2.toFinset, ∑ y ∈ hA.2.toFinset,
        |f l x - f l y| ^ q • (specProj A x ⊗ₜ[ℂ] specProj A y) := by
      simp_rw [Finset.sum_comm (s := hA.2.toFinset) (t := Finset.univ)]
    _ = ∑ l, costElem q (cfc (f l) A) := by simp_rw [costElem_cfc hA]

private theorem observable_replacement {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    {A : H →L[ℂ] H} (hA : IsFiniteObservable A) :
    ∃ L : List (H →L[ℂ] H), (∀ B ∈ L, IsFiniteObservable B) ∧
      costElem p A = (L.map (costElem q)).sum := by
  classical
  letI : Fintype (spectrum ℝ A) := hA.2.fintype
  obtain ⟨k, v, hv⟩ := finite_distance_decomposition hp hpq
    (fun x : spectrum ℝ A => (x : ℝ))
  let f : Fin k → ℝ → ℝ := fun l x =>
    if hx : x ∈ spectrum ℝ A then v l ⟨x, hx⟩ else 0
  let L := List.ofFn fun l : Fin k => cfc (f l) A
  refine ⟨L, ?_, ?_⟩
  · intro B hB
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hB
    exact finiteObservable_cfc hA _
  · have he : costElem p A = ∑ l, costElem q (cfc (f l) A) := by
      apply costElem_of_decomposition hA p q f
      intro x hx y hy
      have hx' := hA.2.mem_toFinset.mp hx
      have hy' := hA.2.mem_toFinset.mp hy
      simpa only [f, dif_pos hx', dif_pos hy'] using hv ⟨x, hx'⟩ ⟨y, hy'⟩
    simpa only [L, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using he

private theorem family_replacement {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (L : List (H →L[ℂ] H)) (hL : ∀ A ∈ L, IsFiniteObservable A) :
    ∃ M : List (H →L[ℂ] H), (∀ B ∈ M, IsFiniteObservable B) ∧
      (L.map (costElem p)).sum = (M.map (costElem q)).sum := by
  induction L with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons A L ih =>
    obtain ⟨N, hN, hA⟩ := observable_replacement hp hpq (hL A (by simp))
    obtain ⟨M, hM, hLM⟩ := ih (fun B hB => hL B (by simp [hB]))
    refine ⟨N ++ M, ?_, ?_⟩
    · intro B hB
      rcases List.mem_append.mp hB with hB | hB
      · exact hN B hB
      · exact hM B hB
    · simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, hA, hLM]

/-- Conjecture 9 for all finite positive orders, on arbitrary complex Hilbert spaces. -/
theorem result {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    costCone (H := H) p ⊆ costCone q := by
  rcases hpq.eq_or_lt with he | hlt
  · subst q
    exact Set.Subset.rfl
  · rintro C ⟨L, hL, rfl⟩
    obtain ⟨M, hM, hcost⟩ := family_replacement hp hlt L hL
    exact ⟨M, hM, hcost⟩

#print axioms result

end D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

end
end MonotonicityHelpers
