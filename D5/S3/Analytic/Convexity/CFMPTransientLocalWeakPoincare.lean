import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Source-only candidate for Mathlib db584cd6d46c92f209a44c0f1c829460d327499d,
Lean 4.33.0. No elaboration, compiler, kernel, or axiom acceptance is claimed.

The extension directly reuses `LipschitzOnWith.extend_finite_dimension`.
The final theorem retains the original open-set, actual a.e. derivative hypothesis.
Downstream estimates consume `lipschitzExtensionConstant E * K`;
the domain and volume measure are never transported.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Metric MeasureTheory ContinuousLinearMap Module
open scoped Topology NNReal ENNReal Convolution

namespace LocalWeakPoincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Open-set equality transfers the given actual derivatives, without selecting them. -/
theorem transfer_ae_actual_derivatives {G H : E → E} {Ω : Set E}
    (hΩ : IsOpen Ω) (heq : EqOn H G Ω)
    (hae : ∀ᵐ y ∂volume.restrict Ω,
      ∃ A : E →L[ℝ] E, HasFDerivAt G A y ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) :
    ∀ᵐ y ∂volume, y ∈ Ω →
      ∃ A : E →L[ℝ] E, HasFDerivAt H A y ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) := by
  rw [ae_restrict_iff' hΩ.measurableSet] at hae
  filter_upwards [hae] with y hy
  intro hyΩ
  obtain ⟨A, hA, hsym⟩ := hy hyΩ
  refine ⟨A, hA.congr_of_eventuallyEq ?_, hsym⟩
  filter_upwards [hΩ.mem_nhds hyΩ] with z hz
  exact heq hz

/-- The reversed convolution makes the smooth factor the right input. -/
def mollify (H : E → E) (φ : E → ℝ) : E → E :=
  H ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume] φ

/-- Smoothness is supplied directly by compactly supported convolution. -/
theorem contDiff_mollify {H : E → E} {φ : E → ℝ} {n : ℕ∞}
    (hH : Continuous H) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (mollify H φ) := by
  exact hφs.contDiff_convolution_right
    (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip hH.locallyIntegrable hφ

/-- Scalar evaluation of the convolution derivative, with integrability of the
canonical weighted line derivative. The test derivative in direction `-u` has
two cancelling minus signs. The integrability output is used by the symmetry proof. -/
theorem mollify_lineDeriv {H : E → E} {K : ℝ≥0} (hH : LipschitzWith K H)
    {φ : E → ℝ} (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 1 φ)
    (x u v : E) :
    Integrable (fun y ↦ lineDeriv ℝ (fun z ↦ inner ℝ v (H z)) y u * φ (x - y)) ∧
      inner ℝ v (fderiv ℝ (mollify H φ) x u) =
        ∫ y, lineDeriv ℝ (fun z ↦ inner ℝ v (H z)) y u * φ (x - y) := by
  let L : E →L[ℝ] ℝ →L[ℝ] E :=
    (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip
  have hscalar : LipschitzWith (‖innerSL ℝ v‖₊ * K)
      (fun y ↦ inner ℝ v (H y)) :=
    (innerSL ℝ v).lipschitz.comp hH
  have htest_s : HasCompactSupport (fun y ↦ φ (x - y)) :=
    hφs.comp_homeomorph (Homeomorph.subLeft x)
  have htest_c : ContDiff ℝ 1 (fun y ↦ φ (x - y)) :=
    hφ.comp (contDiff_const.sub contDiff_id)
  obtain ⟨D, htest_lip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport htest_s htest_c one_ne_zero
  have hweighted : Integrable
      (fun y ↦ lineDeriv ℝ (fun z ↦ inner ℝ v (H z)) y u * φ (x - y)) := by
    simpa only [smul_eq_mul] using
      MeasureTheory.LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (hscalar.locallyIntegrable_lineDeriv (μ := volume) u) htest_c.continuous htest_s
  refine ⟨hweighted, ?_⟩
  have hsign (y : E) :
      lineDeriv ℝ (fun z ↦ φ (x - z)) y (-u) = fderiv ℝ φ (x - y) u := by
    have hchain := (hφ.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      sub_apply, zero_apply, neg_apply,
      ContinuousLinearMap.id_apply, zero_sub, neg_neg] using
      (hchain.hasLineDerivAt (-u)).lineDeriv
  have hibp := hscalar.integral_lineDeriv_mul_eq (μ := volume) htest_lip htest_s u
  simp_rw [hsign] at hibp
  have hd : HasFDerivAt (mollify H φ)
      ((H ⋆[L.precompR E, volume] fderiv ℝ φ) x) x :=
    hφs.hasFDerivAt_convolution_right L hH.continuous.locallyIntegrable hφ x
  have hDi : Integrable (fun y ↦
      (L.precompR E) (H y) (fderiv ℝ φ (x - y))) :=
    (hφs.fderiv ℝ).convolutionExists_right (L.precompR E)
      hH.continuous.locallyIntegrable (hφ.continuous_fderiv one_ne_zero) x
  have hEi : Integrable (fun y ↦
      (L.precompR E) (H y) (fderiv ℝ φ (x - y)) u) :=
    (ContinuousLinearMap.apply ℝ E u).integrable_comp hDi
  rw [hd.fderiv]
  change inner ℝ v ((∫ y,
    (L.precompR E) (H y) (fderiv ℝ φ (x - y))) u) = _
  rw [ContinuousLinearMap.integral_apply hDi u]
  change (innerSL ℝ v) (∫ y,
    (L.precompR E) (H y) (fderiv ℝ φ (x - y)) u) = _
  rw [← (innerSL ℝ v).integral_comp_comm hEi]
  change (∫ y, inner ℝ v (fderiv ℝ φ (x - y) u • H y)) = _
  simp_rw [real_inner_smul_right]
  exact hibp.symm

/-- Fixed directions precede the a.e. argument. Only the closed sampling support
uses the good set; no derivative symmetry is asserted outside it. -/
theorem mollify_symmetric {H : E → E} {K : ℝ≥0} (hH : LipschitzWith K H)
    {Ω : Set E}
    (hae : ∀ᵐ y ∂volume, y ∈ Ω →
      ∃ A : E →L[ℝ] E, HasFDerivAt H A y ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    {φ : E → ℝ} (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 1 φ)
    (x : E) (hsample : tsupport (fun y ↦ φ (x - y)) ⊆ Ω) (u v : E) :
    inner ℝ (fderiv ℝ (mollify H φ) x u) v =
      inner ℝ (fderiv ℝ (mollify H φ) x v) u := by
  obtain ⟨hiuv, huv⟩ := mollify_lineDeriv hH hφs hφ x u v
  obtain ⟨hivu, hvu⟩ := mollify_lineDeriv hH hφs hφ x v u
  rw [real_inner_comm v (fderiv ℝ (mollify H φ) x u),
    real_inner_comm u (fderiv ℝ (mollify H φ) x v), huv, hvu]
  apply sub_eq_zero.mp
  rw [← integral_sub hiuv hivu]
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with y hy
  change lineDeriv ℝ (fun z ↦ inner ℝ v (H z)) y u * φ (x - y) -
    lineDeriv ℝ (fun z ↦ inner ℝ u (H z)) y v * φ (x - y) = (0 : ℝ)
  by_cases hzero : φ (x - y) = 0
  · simp only [hzero, mul_zero, sub_self]
  have hyΩ : y ∈ Ω := hsample (subset_tsupport _ hzero)
  obtain ⟨A, hA, hsym⟩ := hy hyΩ
  have hv : lineDeriv ℝ (fun z ↦ inner ℝ v (H z)) y u = inner ℝ v (A u) := by
    exact (((innerSL ℝ v).hasFDerivAt.comp y hA).hasLineDerivAt u).lineDeriv
  have hu : lineDeriv ℝ (fun z ↦ inner ℝ u (H z)) y v = inner ℝ u (A v) := by
    exact (((innerSL ℝ u).hasFDerivAt.comp y hA).hasLineDerivAt v).lineDeriv
  have hcross : inner ℝ v (A u) = inner ℝ u (A v) :=
    (real_inner_comm (A u) v).trans (hsym u v)
  rw [hv, hu, hcross, sub_self]

/-- A concrete normalized-kernel radius schedule; it also works on the zero space. -/
def shrinkingBump (r : ℝ) (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (r / ((n : ℝ) + 1)) / 2
  rOut := r / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < r / ((n : ℝ) + 1) := by positivity
    linarith

theorem shrinkingBump_rOut_le (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (shrinkingBump (E := E) r hr n).rOut ≤ r := by
  change r / ((n : ℝ) + 1) ≤ r
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
  nlinarith [mul_nonneg hr.le (Nat.cast_nonneg (α := ℝ) n)]

theorem shrinkingBump_rOut_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n ↦ (shrinkingBump (E := E) r hr n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r

/-- Closed support, including its boundary, stays in the original good neighborhood. -/
theorem sampling_support_subset_ball {z₀ x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ ball z₀ r) (φ : ContDiffBump (0 : E)) (hφr : φ.rOut ≤ r) :
    tsupport (fun y ↦ φ.normed volume (x - y)) ⊆ ball z₀ (3 * r) := by
  intro y hy
  change y ∈ tsupport (φ.normed volume ∘ Homeomorph.subLeft x) at hy
  rw [tsupport_comp_eq_preimage, φ.tsupport_normed_eq] at hy
  change dist (x - y) (0 : E) ≤ φ.rOut at hy
  have hxy : dist y x ≤ φ.rOut := by
    calc
      dist y x = dist x y := dist_comm _ _
      _ = dist (x - y) (0 : E) := by simp only [dist_eq_norm_sub, sub_zero]
      _ ≤ φ.rOut := hy
  have hx' : dist x z₀ < r := hx
  show dist y z₀ < 3 * r
  calc
    dist y z₀ ≤ dist y x + dist x z₀ := dist_triangle _ _ _
    _ < 3 * r := by linarith

/-- Quantitative bump approximation uses the true global extension constant. -/
theorem norm_mollify_sub_le {H : E → E} {K : ℝ≥0} (hH : LipschitzWith K H)
    (φ : ContDiffBump (0 : E)) (x : E) :
    ‖mollify H (φ.normed volume) x - H x‖ ≤ (K : ℝ) * φ.rOut := by
  have h := φ.dist_normed_convolution_le (μ := volume) hH.continuous.aestronglyMeasurable
    (x₀ := x) (ε := (K : ℝ) * φ.rOut) (fun y hy ↦
      (hH.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le K.2))
  simpa only [mollify, convolution_flip, dist_eq_norm] using h

/-- Continuity pays interval integrability for every total segment integral. -/
theorem curveIntegrable_segment_of_continuous {ω : E → E →L[ℝ] ℝ}
    (hω : Continuous ω) (a b : E) : CurveIntegrable ω (Path.segment a b) := by
  rw [curveIntegrable_segment]
  have hc : Continuous (fun t : ℝ ↦ ω (AffineMap.lineMap a b t) (b - a)) :=
    (hω.comp (by fun_prop)).clm_apply continuous_const
  exact hc.intervalIntegrable 0 1

/-- A uniform vector-field error bounds the error in each actual segment integral. -/
theorem segment_integral_error {F H : E → E} (hF : Continuous F) (hH : Continuous H)
    {ε : ℝ} (hbound : ∀ z, ‖F z - H z‖ ≤ ε) (a b : E) :
    ‖curveIntegral (fun z ↦ innerSL ℝ (F z)) (Path.segment a b) -
      curveIntegral (fun z ↦ innerSL ℝ (H z)) (Path.segment a b)‖ ≤ ε * ‖b - a‖ := by
  have hωF : Continuous (fun z ↦ innerSL ℝ (F z)) := (innerSL ℝ).continuous.comp hF
  have hωH : Continuous (fun z ↦ innerSL ℝ (H z)) := (innerSL ℝ).continuous.comp hH
  rw [← curveIntegral_fun_sub
    (curveIntegrable_segment_of_continuous hωF a b)
    (curveIntegrable_segment_of_continuous hωH a b)]
  apply norm_curveIntegral_segment_le
  intro z _hz
  rw [← map_sub, innerSL_apply_norm]
  exact hbound z

/-- Only three real segment integrals will be passed to a limit. -/
theorem tendsto_segment_mollify {H : E → E} {K : ℝ≥0} (hH : LipschitzWith K H)
    {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0)) (a b : E) :
    Tendsto (fun n ↦ curveIntegral
      (fun z ↦ innerSL ℝ (mollify H ((φ n).normed volume) z)) (Path.segment a b)) atTop
      (𝓝 (curveIntegral (fun z ↦ innerSL ℝ (H z)) (Path.segment a b))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ ↦ (K : ℝ) * (φ n).rOut * ‖b - a‖)
    (fun _ ↦ norm_nonneg _) ?_ ?_
  · intro n
    exact segment_integral_error
      (contDiff_mollify (n := 1) hH.continuous (φ n).hasCompactSupport_normed
        (φ n).contDiff_normed).continuous
      hH.continuous (norm_mollify_sub_le hH (φ n)) a b
  · simpa only [mul_zero, zero_mul] using (hφ.const_mul (K : ℝ)).mul_const ‖b - a‖

/-- The weak-to-classical bridge at the level of finite segment identities. -/
theorem segment_add_of_ae_symmetric {H : E → E} {K : ℝ≥0}
    (hH : LipschitzWith K H) {z₀ : E} {r : ℝ} (hr : 0 < r)
    (hae : ∀ᵐ y ∂volume, y ∈ ball z₀ (3 * r) →
      ∃ A : E →L[ℝ] E, HasFDerivAt H A y ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    {a b c : E} (ha : a ∈ ball z₀ r) (hb : b ∈ ball z₀ r) (hc : c ∈ ball z₀ r) :
    curveIntegral (fun z ↦ innerSL ℝ (H z)) (Path.segment a b) +
      curveIntegral (fun z ↦ innerSL ℝ (H z)) (Path.segment b c) =
        curveIntegral (fun z ↦ innerSL ℝ (H z)) (Path.segment a c) := by
  let φ : ℕ → ContDiffBump (0 : E) := shrinkingBump r hr
  let M : ℕ → E → E := fun n ↦ mollify H ((φ n).normed volume)
  let ω : ℕ → E → E →L[ℝ] ℝ := fun n z ↦ innerSL ℝ (M n z)
  let dω : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun n z ↦
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp (fderiv ℝ (M n) z)
  have hM (n : ℕ) : ContDiff ℝ 1 (M n) :=
    contDiff_mollify hH.continuous (φ n).hasCompactSupport_normed (φ n).contDiff_normed
  have hdω (n : ℕ) (x : E) : HasFDerivAt (ω n) (dω n x) x :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hM n).differentiable one_ne_zero x).hasFDerivAt
  have hsym (n : ℕ) (x : E) (hx : x ∈ ball z₀ r) (u v : E) :
      dω n x u v = dω n x v u := by
    exact mollify_symmetric hH hae (φ n).hasCompactSupport_normed (φ n).contDiff_normed x
      (sampling_support_subset_ball hr hx (φ n) (shrinkingBump_rOut_le r hr n)) u v
  have hadd (n : ℕ) :
      curveIntegral (ω n) (Path.segment a b) + curveIntegral (ω n) (Path.segment b c) =
        curveIntegral (ω n) (Path.segment a c) :=
    (convex_ball z₀ r).curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
      (fun x _hx ↦ (hdω n x).hasFDerivWithinAt)
      (fun x hx u _hu v _hv ↦ hsym n x hx u v) ha hb hc
  have hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0) := shrinkingBump_rOut_tendsto r hr
  have hab := tendsto_segment_mollify hH hφ a b
  have hbc := tendsto_segment_mollify hH hφ b c
  have hac := tendsto_segment_mollify hH hφ a c
  change Tendsto (fun n ↦ curveIntegral (ω n) (Path.segment a b)) _ _ at hab
  change Tendsto (fun n ↦ curveIntegral (ω n) (Path.segment b c)) _ _ at hbc
  change Tendsto (fun n ↦ curveIntegral (ω n) (Path.segment a c)) _ _ at hac
  have hsum : Tendsto
      (fun n ↦ curveIntegral (ω n) (Path.segment a b) +
        curveIntegral (ω n) (Path.segment b c)) atTop
      (𝓝 (curveIntegral (fun z ↦ innerSL ℝ (H z)) (Path.segment a c))) := by
    simpa only [hadd] using hac
  exact tendsto_nhds_unique (hab.add hbc) hsum

/-- Exact original local weak-Poincaré target, with normalization.

There is no nontriviality assumption on `E` and no positivity assumption on `K`.
The only convex set used is the produced ball. The potential is defined on all
of `E` by a segment integral of a continuous global extension.
-/
theorem exists_local_normalized_primitive {G : E → E} {Ω : Set E} {K : ℝ≥0}
    (hΩ : IsOpen Ω) (hG : LipschitzOnWith K G Ω)
    (hae : ∀ᵐ z ∂volume.restrict Ω,
      ∃ A : E →L[ℝ] E, HasFDerivAt G A z ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (z₀ : E) (hz₀ : z₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ Ω ∧
      ∃ Q : E → ℝ, Q z₀ = 0 ∧
        ∀ z ∈ ball z₀ r, HasFDerivAt Q (innerSL ℝ (G z)) z := by
  classical
  obtain ⟨H, hH, hGH⟩ := hG.extend_finite_dimension
  have heq : EqOn H G Ω := fun _ hx ↦ (hGH hx).symm
  have hHae := transfer_ae_actual_derivatives hΩ heq hae
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  let r : ℝ := δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hlarge : ball z₀ (3 * r) ⊆ Ω := by
    apply Set.Subset.trans (Metric.ball_subset_ball ?_) hδΩ
    dsimp [r]
    linarith
  have hsmall : ball z₀ r ⊆ Ω := by
    apply Set.Subset.trans (Metric.ball_subset_ball ?_) hlarge
    linarith
  have hlocalAE : ∀ᵐ y ∂volume, y ∈ ball z₀ (3 * r) →
      ∃ A : E →L[ℝ] E, HasFDerivAt H A y ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) := by
    filter_upwards [hHae] with y hy
    exact fun hyball ↦ hy (hlarge hyball)
  let ω : E → E →L[ℝ] ℝ := fun z ↦ innerSL ℝ (H z)
  let Q : E → ℝ := fun z ↦ curveIntegral ω (Path.segment z₀ z)
  have hω : Continuous ω := (innerSL ℝ).continuous.comp hH.continuous
  refine ⟨r, hr, hsmall, Q, ?_, ?_⟩
  · simp only [Q, Path.segment_same, curveIntegral_refl]
  · intro z hz
    have hsource : HasFDerivAt (fun y ↦ curveIntegral ω (Path.segment z y)) (ω z) z :=
      HasFDerivAt.curveIntegral_segment_source hω
    have hloc : Q =ᶠ[𝓝 z] (fun y ↦ Q z + curveIntegral ω (Path.segment z y)) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact (segment_add_of_ae_symmetric hH hr hlocalAE (mem_ball_self hr) hz hy).symm
    have hQ : HasFDerivAt Q (ω z) z :=
      (hsource.const_add (Q z)).congr_of_eventuallyEq hloc
    simpa only [ω, heq (hsmall hz)] using hQ

end LocalWeakPoincare
