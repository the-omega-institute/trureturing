/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphic exact signed Taylor selectors for the native Gaussian. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitCovariance

/-! Holomorphic exact signed Taylor selectors for the native Gaussian. -/

set_option maxRecDepth 4096

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlitMean

open Filter
open scoped Topology NNReal
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalFourMSignedOverlap
open private coefficient_of_hasSum norm_sq_lt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open LatticeGeneratingFieldLocality LatticeHalfFock OriginalGaussianExternalBlocks OriginalCurrentMetric

private def directional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (f : E → ℂ) (x : E) : ℂ := fderiv ℂ f x v

private theorem analytic_directional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (v : E) :
    AnalyticAt ℂ (directional v f) x :=
  (ContinuousLinearMap.apply ℂ ℂ v).analyticAt (fderiv ℂ f x) |>.comp hf.fderiv

private def firstDirection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] : ℂ →L[ℂ] ℂ × E :=
  ContinuousLinearMap.inl ℂ ℂ E

private theorem iteratedDeriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ × E → ℂ} {x : ℂ} {y : E} (hf : AnalyticAt ℂ f (x, y)) (n : ℕ) :
    iteratedDeriv n (fun u => f (u, y)) x =
      ((directional (E := ℂ × E) (1, 0))^[n] f) (x, y) := by
  induction n generalizing f x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hs : ∀ᶠ u in 𝓝 x, AnalyticAt ℂ f (u, y) :=
      (show ContinuousAt (fun u : ℂ => (u, y)) x by fun_prop).tendsto.eventually hf.eventually_analyticAt
    have he : deriv (fun u => f (u, y)) =ᶠ[𝓝 x] fun u => directional (1, 0) f (u, y) := by
      filter_upwards [hs] with u hu
      have ha : HasDerivAt (fun t : ℂ => (t, y)) ((1, 0) : ℂ × E) u :=
        by simpa [firstDirection, ContinuousLinearMap.inl_apply] using
          (((firstDirection (E := E)).hasFDerivAt (x := u)).add_const (0, y)).hasDerivAt
      exact (hu.differentiableAt.hasFDerivAt.comp_hasDerivAt u ha).deriv
    rw [he.iteratedDeriv_eq n]
    exact ih (analytic_directional hf _)

private theorem analytic_coefficient_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ × E → ℂ} {y : E} (hf : AnalyticAt ℂ f (0, y)) (n : ℕ) :
    AnalyticAt ℂ (fun t => coefficient n (fun u => f (u, t))) y := by
  have hit (k : ℕ) : AnalyticAt ℂ (((directional (E := ℂ × E) (1, 0))^[k]) f) (0, y) := by
    induction k with
    | zero => exact hf
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact analytic_directional ih _
  have hsection : AnalyticAt ℂ (fun t : E => ((0 : ℂ), t)) y :=
    analyticAt_const.prod analyticAt_id
  apply ((hit n).comp hsection |>.div_const (c := (n.factorial : ℂ))).congr
  have hnear : ∀ᶠ t in 𝓝 y, AnalyticAt ℂ f (0, t) :=
    hsection.continuousAt.tendsto.eventually hf.eventually_analyticAt
  filter_upwards [hnear] with t ht
  exact congrArg (fun z : ℂ => z / (n.factorial : ℂ)) (iteratedDeriv_slice ht n).symm

/-- The scalar factor of the original charge-linear mean at a signed label. -/
def slitMeanEntry (l e : Bool) (p : ℕ) (r : ℂ) : ℂ :=
  coefficient p (fun u => -legSign l * slitMean e u r / slitPeriod r)

theorem slitMeanEntry_analyticOnNhd (l e : Bool) (p : ℕ) :
    AnalyticOnNhd ℂ (slitMeanEntry l e p) slitDomain := by
  intro r hr
  have hf : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      -legSign l * slitMean e z.1 z.2 / slitPeriod z.2) (0, r) :=
    (analyticAt_const.mul (slitMean_joint_analytic e hr)).div
      ((slitPeriod_analyticOnNhd r hr).comp_of_eq
        (f := fun z : ℂ × ℂ => z.2) analyticAt_snd rfl) (slitPeriod_ne_zero hr)
  exact analytic_coefficient_slice hf p

/-- The covariance entry obtained by the literal iterated Taylor selectors. -/
def slitCovarianceEntry (D : LatticeData) (l k : Bool) (x y : External D) (r : ℂ) : ℂ :=
  coefficient y.2.2 (fun v => coefficient x.2.2 (fun u =>
    gramComplex D x.2.1 y.2.1 * slitCovariance l k x.1 y.1 u v r))

theorem slitCovarianceEntry_analyticOnNhd (D : LatticeData) (l k : Bool) (x y : External D) :
    AnalyticOnNhd ℂ (slitCovarianceEntry D l k x y) slitDomain := by
  intro r hr
  have hf : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ =>
      gramComplex D x.2.1 y.2.1 * slitCovariance l k x.1 y.1 p.1 p.2.1 p.2.2) (0, 0, r) :=
    analyticAt_const.mul (slitCovariance_joint_analytic l k x.1 y.1 hr)
  exact analytic_coefficient_slice (analytic_coefficient_slice hf x.2.2) y.2.2

private theorem small_for_norm {r : ℂ} (hr : ‖r‖ < 1) :
    ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ + ‖r‖ < 1 :=
  (isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds (by simpa using hr)

private theorem coefficient_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) (n : ℕ) :
    coefficient n f = coefficient n g :=
  congrArg (fun z : ℂ => z / (n.factorial : ℂ)) (h.iteratedDeriv_eq n)

theorem slitCovarianceEntry_eq_native (D : LatticeData) {X : Type*} (label : X → External D)
    (l k : Bool) (x y : X) {w : ℂ} (hw : ‖w‖ < 1) :
    slitCovarianceEntry D l k (label x) (label y) (w ^ 2) =
      explicitEffectiveKernel D label w (taggedMode l x) (taggedMode k y) := by
  rw [native_tagged_entry D label l k x y hw, slitCovarianceEntry]
  have hs := small_for_norm (norm_sq_lt hw)
  apply coefficient_congr
  filter_upwards [hs] with v hv
  apply coefficient_congr
  filter_upwards [hs] with u hu
  rw [slitCovariance_eq_native l k _ _ hu hv]

theorem slitMeanEntry_eq_native (D : LatticeData) (a : Charge D) {X : Type*} [Fintype X]
    [DecidableEq X] (label : X → External D) (l : Bool) (x : X) {w : ℂ} (hw : ‖w‖ < 1) :
    (bilinear D (unitCharge D (label x).2.1) a : ℂ) *
      slitMeanEntry l (label x).1 (label x).2.2 (w ^ 2) =
      OriginalGaussianSewnAnalytic.explicitMean D a label w (taggedMode l x) := by
  let e := (label x).1
  let p := (label x).2.2
  let c := -legSign l / slitPeriod (w ^ 2)
  let R : ℝ≥0 := ⟨(1 - ‖w ^ 2‖) / 2, by
    have h := norm_sq_lt hw
    linarith⟩
  have hR : 0 < R := by
    change 0 < (1 - ‖w ^ 2‖) / 2
    have h := norm_sq_lt hw
    linarith
  have hsmall : ‖(R : ℂ)‖ + ‖w ^ 2‖ < 1 := by
    change ‖((R : ℝ) : ℂ)‖ + ‖w ^ 2‖ < 1
    rw [Complex.norm_real, Real.norm_of_nonneg R.coe_nonneg]
    change (1 - ‖w ^ 2‖) / 2 + ‖w ^ 2‖ < 1
    have h := norm_sq_lt hw
    linarith
  let A := OriginalGaussianSourceEvaluation.sourceAmplitude e
  have hsum (u : ℂ) (hu : ‖u‖ + ‖w ^ 2‖ < 1) :
      HasSum (fun j : ℕ => A j (w ^ 2) * u ^ j) (slitMean e u (w ^ 2)) := by
    rw [slitMean_eq_sourceMode e hu]
    unfold A OriginalGaussianExternalGenerators.sourceMode
    cases e
    · exact (OriginalGaussianExternalGenerators.sourceAmplitude_generators hu).2.summable.hasSum
    · exact (OriginalGaussianExternalGenerators.sourceAmplitude_generators hu).1.summable.hasSum
  have hcoef : slitMeanEntry l e p (w ^ 2) = c * A p (w ^ 2) := by
    unfold slitMeanEntry
    refine coefficient_of_hasSum (a := fun n => c * A n (w ^ 2)) hR ?_ ?_ p
    · have h := ((hsum R hsmall).mul_left c).summable.norm
      simpa only [mul_assoc] using h
    · filter_upwards [small_for_norm (norm_sq_lt hw)] with u hu
      have hval : c * slitMean e u (w ^ 2) = -legSign l * slitMean e u (w ^ 2) /
          slitPeriod (w ^ 2) := by simp only [c, div_eq_mul_inv]; ring
      rw [← hval]
      simpa only [mul_assoc] using (hsum u hu).mul_left c
  rw [native_mean D a label l x hw]
  change _ * slitMeanEntry l e p (w ^ 2) = _
  rw [hcoef]
  cases l <;> simp [A, c, e, p, legSign, slitPeriod_eq_period (norm_sq_lt hw)] <;> ring <;> simp

#print axioms slitMeanEntry_eq_native
#print axioms slitCovarianceEntry_eq_native
#print axioms slitMeanEntry_analyticOnNhd
#print axioms slitCovarianceEntry_analyticOnNhd

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlitMean
