/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native signed covariance and mean in the original elliptic overlap. -/

import D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
import Mathlib.Analysis.Analytic.Uniqueness

noncomputable section
open scoped Topology ENNReal NNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSignedOverlap

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalGaussianExternalBlocks OriginalGaussianExternalResolvent OriginalCurrentMetric
open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalGenerators
open OriginalGaussianExternalModeSums
open private candidateJ_chart from D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial
open OriginalGaussianExternalSignedCandidate
open OriginalGaussianExternalAnalyticCandidate (b correction)
open OriginalGaussianSewnAnalytic (explicitMean coefficient)
open OriginalGaussianSourceEvaluation
open D5.S3.Analytic.OriginalHalfBinomialPeriod

/-- The two native legs, with the left leg first as in the sewn Gaussian. -/
def taggedMode {X : Type*} (right : Bool) (x : X) : X ⊕ X :=
  if right then .inr x else .inl x

private theorem tagged_covariance (D : LatticeData) {X : Type*}
    (label : X → External D) (l k : Bool) (x y : X) {w : ℂ} (hw : ‖w‖ < 1) :
    explicitEffectiveKernel D label w (taggedMode l x) (taggedMode k y) =
      gramComplex D (label x).2.1 (label y).2.1 *
        (if l = k then externalFreeEntry D (label x) (label y) +
          externalJ (label x).1 (label x).2.2 (label y).1 (label y).2.2 w
        else -externalT (label x).1 (label x).2.2 (label y).1 (label y).2.2 w) := by
  cases l <;> cases k
  · rfl
  · unfold taggedMode explicitEffectiveKernel
    change -gramComplex D _ _ * _ = gramComplex D _ _ * -_
    ring
  · have hT := OriginalGaussianExternalEquations.literal_symmetry true
        (label y).1 (label x).1 (label y).2.2 (label x).2.2 hw
    simp only [ite_true] at hT
    unfold taggedMode explicitEffectiveKernel
    change -((D.G (label y).2.1 (label x).2.1 : ℤ) : ℂ) *
      externalT (label y).1 (label y).2.2 (label x).1 (label x).2.2 w =
      (D.G (label x).2.1 (label y).2.1 : ℂ) *
        -externalT (label x).1 (label x).2.2 (label y).1 (label y).2.2 w
    rw [D.symmetric (label y).2.1 (label x).2.1, hT]
    ring
  · rfl

private theorem free_diagonal_sum (D : LatticeData) (e f : Bool) (i j : Fin D.rank)
    {u v : ℂ} (huv : ‖u * v‖ < 1) :
    HasSum (fun pq : ℕ × ℕ => externalFreeEntry D (e, i, pq.1) (f, j, pq.2) *
        u ^ pq.1 * v ^ pq.2)
      (if e = f then 0 else cauchy e f u v) := by
  by_cases hef : e = f
  · simp [externalFreeEntry, hef]
  let diag : ℕ → ℕ × ℕ := fun n => (n, n)
  have hinj : Function.Injective diag := fun _ _ h => congrArg Prod.fst h
  have hgeo := hasSum_geometric_of_norm_lt_one huv
  have hweighted := (hasSum_choose_mul_geometric_of_norm_lt_one 1 huv).sub
    (hgeo.mul_left (1 / 2 : ℂ))
  have hden : 1 - u * v ≠ 0 := by
    intro h
    have hh := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one] at hh
    linarith
  have hs : HasSum (fun n : ℕ => -((n : ℂ) + 1 / 2) * (u * v) ^ n)
      (cauchy e f u v) := by
    convert hweighted.neg using 1
    · funext n
      simp [Nat.choose_one_right] <;> ring
    · simp only [cauchy, rho, G, hef, ite_false]
      field_simp
      ring
  rw [ite_eq_right hef]
  have hsExt := (hasSum_extend_zero hinj).mpr hs
  apply hsExt.congr_fun
  rintro ⟨p,q⟩
  by_cases hpq : p = q
  · subst q
    rw [show (p,p) = diag p by rfl, hinj.extend_apply]
    simp [externalFreeEntry, diag, hef, mul_pow, mul_assoc]
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨n, hn⟩
      exact hpq ((congrArg Prod.fst hn).symm.trans (congrArg Prod.snd hn)))]
    simp [externalFreeEntry, hef, hpq]

/-- The spatial generator read by the actual two tagged Gaussian legs. -/
def covarianceMode (l k e f : Bool) (u v r : ℂ) : ℂ :=
  if l = k then candidateJ e f u v r + (if e = f then 0 else cauchy e f u v)
  else -candidateT e f u v r

/-- The original matrix entries, including both crossed orders and every
colour and signed mode, are the coefficients of this spatial generator. -/
theorem native_covariance_hasSum (D : LatticeData) (l k e f : Bool) (i j : Fin D.rank)
    {u v w : ℂ} (hu : ‖u‖ + ‖w‖ < 1) (hv : ‖v‖ + ‖w‖ < 1) :
    HasSum (fun pq : ℕ × ℕ =>
      explicitEffectiveKernel D (fun x : Bool =>
        if x then (f, j, pq.2) else (e, i, pq.1)) w
        (taggedMode l false) (taggedMode k true) * u ^ pq.1 * v ^ pq.2)
      (gramComplex D i j * covarianceMode l k e f u v (w ^ 2)) := by
  have hw : ‖w‖ < 1 := by linarith [norm_nonneg u]
  have hu1 : ‖u‖ < 1 := by linarith [norm_nonneg w]
  have hv1 : ‖v‖ < 1 := by linarith [norm_nonneg w]
  have huv : ‖u * v‖ < 1 := by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hu1.le (norm_nonneg v) hv1
  obtain ⟨hj, ht⟩ := OriginalGaussianComplexRadialContinuation.allSignsJT_eq_candidates_complex
    e f hu hv
  have hsum := OriginalGaussianExternalNormal.external_kernel_mode_summable e f hu hv
  have hJ : HasSum (fun pq : ℕ × ℕ =>
      externalJ e pq.1 f pq.2 w * u ^ pq.1 * v ^ pq.2) (candidateJ e f u v (w ^ 2)) := by
    rw [← hj, kernelMode]
    exact ((hsum.1.congr (fun pq => congrArg norm (by ring))).of_norm.hasSum)
  have hT : HasSum (fun pq : ℕ × ℕ =>
      externalT e pq.1 f pq.2 w * u ^ pq.1 * v ^ pq.2) (candidateT e f u v (w ^ 2)) := by
    rw [← ht, kernelMode]
    exact ((hsum.2.congr (fun pq => congrArg norm (by ring))).of_norm.hasSum)
  by_cases h : l = k
  · simp only [covarianceMode, h, ite_true]
    refine ((hJ.add (free_diagonal_sum D e f i j huv)).mul_left _).congr_fun ?_
    intro pq
    rw [tagged_covariance _ _ _ _ _ _ hw]
    simp only [Bool.false_eq_true, ite_false, ite_true, h, Pi.add_apply]
    ring
  · simp only [covarianceMode, h, ite_false]
    refine (hT.neg.mul_left _).congr_fun ?_
    intro pq
    rw [tagged_covariance _ _ _ _ _ _ hw]
    simp only [Bool.false_eq_true, ite_false, ite_true, h, Pi.neg_apply]
    ring

private theorem coefficient_of_hasSum {a : ℕ → ℂ} {F : ℂ → ℂ}
    {R : ℝ≥0} (hR : 0 < R)
    (hs : Summable (fun n => ‖a n * (R : ℂ) ^ n‖))
    (hF : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => a n * z ^ n) (F z)) (n : ℕ) :
    coefficient n F = a n := by
  let s := FormalMultilinearSeries.ofScalars ℂ a
  have hr : (R : ℝ≥0∞) ≤ s.radius := by
    apply s.le_radius_of_summable
    simpa [s, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using hs
  have h0 : 0 < s.radius := (ENNReal.coe_pos.mpr hR).trans_le hr
  have he : s.sum =ᶠ[𝓝 (0 : ℂ)] F := by
    filter_upwards [hF] with z hz
    exact (FormalMultilinearSeries.ofScalars_sum_eq a z).trans (by
      simpa only [smul_eq_mul] using hz.tsum_eq)
  have hp := (s.hasFPowerSeriesOnBall h0).hasFPowerSeriesAt.congr he
  have heq := hp.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  have ht := congrArg (fun t : FormalMultilinearSeries ℂ ℂ ℂ => t.coeff n) heq
  simpa [s, coefficient, FormalMultilinearSeries.coeff_ofScalars] using ht

private theorem coefficient_of_double_hasSum {a : ℕ × ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    {R : ℝ≥0} (hR : 0 < R)
    (hs : ∀ u v : ℂ, ‖u‖ ≤ R → ‖v‖ ≤ R →
      HasSum (fun pq : ℕ × ℕ => a pq * u ^ pq.1 * v ^ pq.2) (F u v)) (p q : ℕ) :
    coefficient q (fun v => coefficient p (fun u => F u v)) = a (p,q) := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hNR : ‖(R : ℂ)‖ = (R : ℝ) := by simp
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ ≤ (R : ℝ) := by
    have hs : IsOpen {z : ℂ | ‖z‖ < (R : ℝ)} := isOpen_lt continuous_norm continuous_const
    filter_upwards [hs.mem_nhds (show ‖(0 : ℂ)‖ < (R : ℝ) by simpa using hR)] with z hz
    exact hz.le
  let row (v : ℂ) (n : ℕ) := ∑' m, a (n,m) * v ^ m
  have hrow (v : ℂ) (hv : ‖v‖ ≤ (R : ℝ)) :
      coefficient p (fun u => F u v) = row v p := by
    apply coefficient_of_hasSum hR
    · have hb := ((hs (R : ℂ) v hNR.le hv).summable.prod).norm
      convert hb using 1
      funext n
      congr 1
      unfold row
      rw [← tsum_mul_right]
      apply tsum_congr
      intro m
      ring
    · filter_upwards [hn] with u hu
      have hh := hs u v hu hv
      have he (n : ℕ) :
          (∑' m, a (n,m) * u ^ n * v ^ m) = row v n * u ^ n := by
        unfold row
        rw [← tsum_mul_right]
        apply tsum_congr
        intro m
        ring
      exact hh.prod_fiberwise (fun n => he n ▸ (hh.summable.prod_factor n).hasSum)
  apply coefficient_of_hasSum hR
  · have hcol := (hs (R : ℂ) (R : ℂ) hNR.le hNR.le).summable.prod_factor p
    have hc := hcol.mul_left (((R : ℂ) ^ p)⁻¹)
    have he (m : ℕ) : ((R : ℂ) ^ p)⁻¹ * (a (p,m) * (R : ℂ) ^ p * (R : ℂ) ^ m) =
        a (p,m) * (R : ℂ) ^ m := by
      field_simp [pow_ne_zero p hR0]
    exact (hc.congr he).norm
  · filter_upwards [hn] with v hv
    rw [hrow v hv]
    unfold row
    have hw := (hs (R : ℂ) v hNR.le hv).summable.prod_factor p
    have hw' := hw.mul_left (((R : ℂ) ^ p)⁻¹)
    refine (hw'.congr ?_).hasSum
    intro m
    field_simp [pow_ne_zero p hR0]

/-- The iterated native Taylor selector recovers the actual matrix entry for
arbitrary fixed external labels, with repeated labels and both orders allowed. -/
theorem native_tagged_entry (D : LatticeData) {X : Type*} (label : X → External D)
    (l k : Bool) (x y : X) {w : ℂ} (hw : ‖w‖ < 1) :
    explicitEffectiveKernel D label w (taggedMode l x) (taggedMode k y) =
      coefficient (label y).2.2 (fun v => coefficient (label x).2.2 (fun u =>
        gramComplex D (label x).2.1 (label y).2.1 *
          covarianceMode l k (label x).1 (label y).1 u v (w ^ 2))) := by
  let R : ℝ≥0 := ⟨(1 - ‖w‖) / 2, by linarith⟩
  have hR : 0 < R := by change 0 < (1 - ‖w‖) / 2; linarith
  let a : ℕ × ℕ → ℂ := fun pq =>
    explicitEffectiveKernel D (fun z : Bool =>
      if z then ((label y).1, (label y).2.1, pq.2) else ((label x).1, (label x).2.1, pq.1))
      w (taggedMode l false) (taggedMode k true)
  have hs (u v : ℂ) (hu : ‖u‖ ≤ (R : ℝ)) (hv : ‖v‖ ≤ (R : ℝ)) :
      HasSum (fun pq => a pq * u ^ pq.1 * v ^ pq.2)
        (gramComplex D (label x).2.1 (label y).2.1 *
          covarianceMode l k (label x).1 (label y).1 u v (w ^ 2)) := by
    change ‖u‖ ≤ (1 - ‖w‖) / 2 at hu
    change ‖v‖ ≤ (1 - ‖w‖) / 2 at hv
    exact native_covariance_hasSum D l k _ _ _ _ (by linarith) (by linarith)
  rw [coefficient_of_double_hasSum hR hs]
  unfold a
  rw [tagged_covariance _ _ _ _ _ _ hw, tagged_covariance _ _ _ _ _ _ hw]
  simp

/-- The actual Gaussian mean in each signed mode and on either native leg. -/
theorem native_mean (D : LatticeData) (a : Charge D) {X : Type*} [Fintype X]
    [DecidableEq X] (label : X → External D) (l : Bool) (x : X) {w : ℂ}
    (hw : ‖w‖ < 1) :
    explicitMean D a label w (taggedMode l x) =
      (if l then 1 else -1) * (bilinear D (unitCharge D (label x).2.1) a : ℂ) *
        (sourceAmplitude (label x).1 (label x).2.2 (w ^ 2) / period (w ^ 2)) := by
  rw [← sourceExternal_evaluation (label x).1 (label x).2.2 hw]
  cases l <;> simp [explicitMean, taggedMode] <;> ring


open OriginalGaussianExternalCandidateCore (rightChart leftChart)
open OriginalFourMActualChart (spatialKernel)
open private spatialNumerator from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart
open OriginalFourMPeriodSource (periodCorrection)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)

private theorem ratJ_spatial (e f : Bool) {u v r : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hg : G e f u v ≠ 0) :
    rationalJ e f u v r = spatialKernel (1 - r) (rightChart e u) (rightChart f v) := by
  have hd : rightChart e u - rightChart f v =
      (if f then -G e f u v else G e f u v) /
        ((if e then u else 1) * (if f then v else 1)) := by
    cases e <;> cases f <;> simp [rightChart, G] <;> field_simp [hu,hv] <;> ring
  rw [spatialKernel, hd]
  unfold rationalJ
  generalize hden : G e f u v = den at hg ⊢
  cases e <;> cases f <;>
    simp only [rightChart, spatialNumerator, Qconstant, jN, h, b, Bool.false_eq_true,
      Bool.true_eq_false, Bool.and_false, Bool.and_true, ite_true, ite_false] <;>
    field_simp [hu, hv, hg] <;> rw [← hden] <;> simp [G] <;> ring

private theorem ratT_spatial (e f : Bool) {u v r : ℂ}
    (hu : u ≠ 0) (hv1 : b v ≠ 0) (he : E e f u v r ≠ 0) :
    rationalT e f u v r = spatialKernel (1 - r) (rightChart e u) (leftChart f r v) := by
  have hd : rightChart e u - leftChart f r v =
      (if e then E e f u v r else -E e f u v r) / ((if e then u else 1) * b v) := by
    have hv : 1 - v ≠ 0 := hv1
    cases e <;> cases f <;>
      simp [rightChart, leftChart, E, K, b] <;> field_simp [hu,hv] <;> ring
  rw [spatialKernel, hd]
  unfold rationalT
  generalize hden : E e f u v r = den at he ⊢
  have hv : 1 - v ≠ 0 := hv1
  cases e <;> cases f <;>
    simp only [rightChart, leftChart, spatialNumerator, N, b, Bool.false_eq_true,
      ite_true, ite_false] <;>
    field_simp [hu, hv, he] <;> rw [← hden] <;> simp [E, K, b] <;> ring

private theorem norm_sq_lt {w : ℂ} (hw : ‖w‖ < 1) : ‖w ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hw (by decide)

private theorem small_sq {u w : ℂ} (hu : ‖u‖ + ‖w‖ < 1) :
    ‖u‖ + ‖w ^ 2‖ < 1 := by
  have hw : ‖w‖ < 1 := by linarith [norm_nonneg u]
  rw [norm_pow, pow_two]
  have h := mul_le_of_le_one_right (norm_nonneg w) hw.le
  linarith

private theorem slit_correction_eq {r : ℂ} (hr : ‖r‖ < 1) :
    correction r = periodCorrection slitPeriod r := by
  have he : period =ᶠ[𝓝 r] slitPeriod := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hr] with t ht
    exact (D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.slitPeriod_eq_period ht).symm
  unfold correction OriginalGaussianExternalAnalyticCandidate.ell periodCorrection
  rw [he.deriv_eq, he.eq_of_nhds, mul_div_assoc]

/-- On the native complex bidisk the mixed free block exactly restores the
subtracted Cauchy kernel. The two crossed orders both carry the leg minus. -/
theorem native_spatial_overlap (e f : Bool) {u v w : ℂ}
    (hu : ‖u‖ + ‖w‖ < 1) (hv : ‖v‖ + ‖w‖ < 1)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hg : G e f u v ≠ 0) :
    let r := w ^ 2
    let m := sourceMode e u r * sourceMode f v r
    let C := periodCorrection slitPeriod r
    (∀ l, covarianceMode l l e f u v r =
        m * (spatialKernel (1 - r) (rightChart e u) (rightChart f v) - C) -
          (if e = f then cauchy e f u v else 0)) ∧
    (∀ l k, l ≠ k → covarianceMode l k e f u v r =
        -m * (spatialKernel (1 - r) (rightChart e u) (leftChart f r v) - C)) := by
  dsimp only
  have hw : ‖w‖ < 1 := by linarith [norm_nonneg u]
  have hc := slit_correction_eq (norm_sq_lt hw)
  have hu' := small_sq hu
  have hv' := small_sq hv
  constructor
  · intro l
    rw [covarianceMode, ite_eq_left rfl, candidateJ_chart e f hu' hv' hg, chartJ,
      ratJ_spatial e f hu0 hv0 hg, hc]
    by_cases h : e = f <;> simp [h]
  · intro l k hlk
    have hb := (mode_factors_ne_zero hv').1
    have hs : Real.sqrt ‖w ^ 2‖ = ‖w‖ := by rw [norm_pow, Real.sqrt_sq (norm_nonneg _)]
    have hE := E_ne_zero e f (u := u) (v := v) (r := w ^ 2) (by simpa only [hs] using hu) (by simpa only [hs] using hv)
    rw [covarianceMode, ite_eq_right hlk, candidateT, ratT_spatial e f hu0 hb hE, hc]
    ring

/-- The genuine same-orientation diagonal has the finite value of the
Cauchy-subtracted J generator, including the puncture value at zero. -/
theorem native_diagonal (l e : Bool) {u w : ℂ} (hu : ‖u‖ + ‖w‖ < 1) :
    let r := w ^ 2
    Tendsto (fun p : ℂ × ℂ => covarianceMode l l e e p.1 p.2 r) (𝓝 (u,u))
      (𝓝 ((r / 4 - periodCorrection slitPeriod r) / (b u * h e u r) +
        r ^ 2 * u / (8 * (b u * h e u r) ^ 2))) := by
  dsimp only
  have hw : ‖w‖ < 1 := by linarith [norm_nonneg u]
  have ha := (candidateJ_joint_analytic e e (small_sq hu) (small_sq hu)).continuousAt
  have he := candidateJ_diagonal e (small_sq hu)
  rw [slit_correction_eq (norm_sq_lt hw)] at he
  simpa [covarianceMode, he] using ha.tendsto


/-- Source orientation is fixed by the opposite means on the two native legs. -/
def legSign (right : Bool) : ℂ := if right then -1 else 1

/-- The normalized derivative of the left or right half-coordinate map. -/
def signedHalfSource (right e : Bool) (u r : ℂ) : ℂ :=
  legSign right * sourceMode e u r

/-- The charge-linear generator at the original signed labels uses the
same oriented source factor as the geometric covariance. -/
theorem native_mean_hasSum (D : LatticeData) (a : Charge D) (l e : Bool)
    (i : Fin D.rank) {u w : ℂ} (hu : ‖u‖ + ‖w‖ < 1) :
    HasSum (fun p : ℕ =>
      explicitMean D a (fun _ : Unit => (e,i,p)) w (taggedMode l ()) * u ^ p)
      (-(bilinear D (unitCharge D i) a : ℂ) *
        signedHalfSource l e u (w ^ 2) / slitPeriod (w ^ 2)) := by
  have hw : ‖w‖ < 1 := by linarith [norm_nonneg u]
  have hs : HasSum (fun p : ℕ => sourceAmplitude e p (w ^ 2) * u ^ p)
      (sourceMode e u (w ^ 2)) := by
    unfold sourceMode
    cases e
    · exact (sourceAmplitude_generators (small_sq hu)).2.summable.hasSum
    · exact (sourceAmplitude_generators (small_sq hu)).1.summable.hasSum
  rw [D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.slitPeriod_eq_period (norm_sq_lt hw)]
  convert (hs.mul_left (-(bilinear D (unitCharge D i) a : ℂ) *
    legSign l / period (w ^ 2))) using 1
  · funext p
    rw [native_mean _ _ _ _ _ hw]
    cases l <;> simp [legSign, div_eq_mul_inv] <;> ring
  · unfold signedHalfSource
    ring

private def nativeHalfX (right e : Bool) (r q : ℂ) : ℂ :=
  if right then leftChart e r (q ^ 2) else rightChart e (q ^ 2)

private def halfSlope (e : Bool) (q : ℂ) : ℂ :=
  if e then -2 * q / (q ^ 2) ^ 2 else 2 * q

private def nativeHalfY (right e : Bool) (r q : ℂ) : ℂ :=
  let u := q ^ 2
  let g := if right then -r / (rightChart e u - 1)^2 else 1
  g * halfSlope e q / (2 * signedHalfSource right e u r)

private theorem halfSlope_deriv (e : Bool) {q : ℂ} (hq : q ≠ 0) :
    HasDerivAt (fun t : ℂ => rightChart e (t ^ 2)) (halfSlope e q) q := by
  cases e
  · simpa [rightChart, halfSlope] using hasDerivAt_pow 2 q
  · simpa [rightChart, halfSlope, one_div, mul_comm, Pi.inv_def] using
      ((hasDerivAt_pow 2 q).inv (pow_ne_zero 2 hq))

private def legMap (r x : ℂ) : ℂ := (x - (1 - r)) / (x - 1)

private theorem legMap_deriv {r x : ℂ} (hx : x - 1 ≠ 0) :
    HasDerivAt (legMap r) (-r / (x - 1)^2) x := by
  unfold legMap
  exact (((hasDerivAt_id x).sub_const (1 - r)).fun_div ((hasDerivAt_id x).sub_const 1) hx).congr_deriv
    (by dsimp; ring)

private theorem legMap_chart (e : Bool) {r u : ℂ} (hu : u ≠ 0) (h1 : u ≠ 1) :
    legMap r (rightChart e u) = leftChart e r u := by
  have hb : 1 - u ≠ 0 := sub_ne_zero.mpr h1.symm
  have hb' : u - 1 ≠ 0 := sub_ne_zero.mpr h1
  cases e <;> simp [legMap, rightChart, leftChart] <;> field_simp [hu,hb,hb'] <;> ring

private def legendre (r x : ℂ) : ℂ := x * (x - 1) * (x-(1 - r))

private theorem legMap_cubic {r x : ℂ} (hx : x - 1 ≠ 0) :
    legendre r (legMap r x) = (-r / (x - 1)^2)^2 * legendre r x := by
  unfold legendre legMap
  field_simp
  ring

/-- At the half-coordinate (u=q ^ 2), the actual source is the coefficient
of the pullback of dx/(2y). The right-hand lift has the reversed orientation. -/
theorem half_coordinate_pullback (right e : Bool) {q r : ℂ}
    (hq : q ≠ 0) (hr : r ≠ 0) (hsmall : ‖q ^ 2‖ + ‖r‖ < 1) :
    let u := q ^ 2
    let x := nativeHalfX right e r q
    let y := nativeHalfY right e r q
    y ^ 2 = legendre r x ∧ y ≠ 0 ∧
      HasDerivAt (nativeHalfX right e r) (2 * y * signedHalfSource right e u r) q := by
  dsimp only
  let u : ℂ := q ^ 2
  have hu : u ≠ 0 := pow_ne_zero 2 hq
  have hb : b u ≠ 0 := (mode_factors_ne_zero hsmall).1
  have hu1 : u ≠ 1 := fun he => hb (by simp [b, he])
  have hx : rightChart e u - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    cases e
    · exact hu1
    · simpa [rightChart, one_div] using (show u⁻¹ ≠ 1 from by simpa using hu1)
  have hh : h e u r ≠ 0 := h_ne_zero e hsmall
  have hm : sourceMode e u r ^ 2 = 1 / (b u * h e u r) := by
    cases e
    · exact (sourceMode_square hsmall).2
    · exact (sourceMode_square hsmall).1
  have hm0 : sourceMode e u r ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide : 2 ≠ 0)] at hm
    exact one_div_ne_zero (mul_ne_zero hb hh) hm.symm
  have hs : halfSlope e q ≠ 0 := by
    cases e <;> simp [halfSlope, hq, pow_ne_zero]
  have hraw : (halfSlope e q / (2 * sourceMode e u r)) ^ 2 =
      legendre r (rightChart e u) := by
    rw [div_pow, mul_pow, hm]
    cases e <;>
      simp only [halfSlope, rightChart, h, b, legendre, Bool.false_eq_true, ite_false, ite_true, u]
        at hb hh ⊢ <;>
      field_simp [hq, hb, hh] <;> ring
  have hder := halfSlope_deriv e hq
  cases right
  · simp only [nativeHalfY, nativeHalfX, signedHalfSource, legSign, Bool.false_eq_true,
      ite_false, one_mul]
    refine ⟨hraw, div_ne_zero hs (mul_ne_zero (by norm_num) hm0), ?_⟩
    change HasDerivAt (fun t => rightChart e (t ^ 2))
      (2 * (halfSlope e q / (2 * sourceMode e u r)) * sourceMode e u r) q
    exact hder.congr_deriv (by field_simp [hm0])
  · have hlocal : (fun t : ℂ => legMap r (rightChart e (t^2))) =ᶠ[𝓝 q]
        nativeHalfX true e r := by
      have ho := (isOpen_ne_fun (continuous_id.pow 2) continuous_const :
        IsOpen {t : ℂ | t ^ 2 ≠ 1}).mem_nhds hu1
      filter_upwards [(isOpen_ne :
        IsOpen {t : ℂ | t ≠ 0}).mem_nhds hq, ho] with t ht ht1
      exact legMap_chart e (pow_ne_zero 2 ht) ht1
    have hyp : -r / (rightChart e u - 1) ^ 2 ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr hr) (pow_ne_zero 2 hx)
    have hdx := (legMap_deriv (r := r) hx).comp q hder
    have hy : nativeHalfY true e r q =
        -(-r / (rightChart e u - 1) ^ 2) * (halfSlope e q / (2 * sourceMode e u r)) := by
      simp [nativeHalfY, signedHalfSource, legSign, u]
      ring
    rw [hy]
    refine ⟨?_, mul_ne_zero (neg_ne_zero.mpr hyp) (div_ne_zero hs (mul_ne_zero (by norm_num) hm0)), ?_⟩
    · rw [nativeHalfX, ite_eq_left rfl, ← legMap_chart e hu hu1, mul_pow, neg_sq, hraw]
      exact (legMap_cubic hx).symm
    · apply (hdx.congr_of_eventuallyEq hlocal.symm).congr_deriv
      have hmSign : signedHalfSource true e (q ^ 2) r = -sourceMode e u r := by
        simp [signedHalfSource, legSign, u]
      rw [hmSign]
      field_simp [hm0, hx] <;> ring

private theorem spatial_legMap {r x X : ℂ} (hr : r ≠ 0)
    (hx : x - 1 ≠ 0) (hX : X - 1 ≠ 0) (hxx : x - X ≠ 0) :
    spatialKernel (1 - r) (legMap r x) (legMap r X) = spatialKernel (1 - r) x X := by
  have hd : legMap r x - legMap r X =
      -r * (x - X) / ((x - 1)*(X - 1)) := by
    unfold legMap
    field_simp
    ring
  unfold spatialKernel
  rw [hd]
  unfold spatialNumerator legMap
  field_simp [hr,hx,hX,hxx]
  ring

private theorem legMap_sub_one {r x : ℂ} (hx : x - 1 ≠ 0) :
    legMap r x - 1 = r / (x - 1) := by
  unfold legMap
  field_simp
  ring

private theorem legMap_involution {r x : ℂ} (hr : r ≠ 0) (hx : x - 1 ≠ 0) :
    legMap r (legMap r x) = x := by
  change (legMap r x - (1 - r)) / (legMap r x - 1) = x
  rw [legMap_sub_one hx]
  unfold legMap
  field_simp [hr,hx]
  ring

/-- Restore only the same-puncture subtraction to expose the geometric
covariance with the actual two signed dx/(2y) factors. -/
theorem native_geometric_covariance (l k e f : Bool) {q Q w : ℂ}
    (hu : ‖q ^ 2‖ + ‖w‖ < 1) (hv : ‖Q ^ 2‖ + ‖w‖ < 1)
    (hq : q ≠ 0) (hQ : Q ≠ 0) (hw : w ≠ 0)
    (hg : G e f (q ^ 2) (Q ^ 2) ≠ 0)
    (hx : rightChart e (q ^ 2) - 1 ≠ 0) (hX : rightChart f (Q ^ 2) - 1 ≠ 0)
    (hxx : rightChart e (q ^ 2) - rightChart f (Q ^ 2) ≠ 0)
    (hcross : rightChart e (q ^ 2) - leftChart f (w ^ 2) (Q ^ 2) ≠ 0) :
    let r := w ^ 2
    let u := q ^ 2
    let v := Q ^ 2
    covarianceMode l k e f u v r + (if l = k ∧ e = f then cauchy e f u v else 0) =
      signedHalfSource l e u r * signedHalfSource k f v r *
        (spatialKernel (1 - r) (nativeHalfX l e r q) (nativeHalfX k f r Q) -
          periodCorrection slitPeriod r) := by
  dsimp only
  have hr := pow_ne_zero 2 hw
  have hu0 := pow_ne_zero 2 hq
  have hv0 := pow_ne_zero 2 hQ
  have hu1 : q ^ 2 ≠ 1 := fun he => (mode_factors_ne_zero (small_sq hu)).1 (by simp [he])
  have hv1 : Q ^ 2 ≠ 1 := fun he => (mode_factors_ne_zero (small_sq hv)).1 (by simp [he])
  obtain ⟨hSame,hCross⟩ := native_spatial_overlap e f hu hv hu0 hv0 hg
  have hgr := legMap_chart e (r := w ^ 2) hu0 hu1
  have hgs := legMap_chart f (r := w ^ 2) hv0 hv1
  have hSameRight := spatial_legMap hr hx hX hxx
  have hCrossRight := spatial_legMap hr hx
    (by rw [legMap_sub_one hX]; exact div_ne_zero hr hX) (hgs.symm ▸ hcross)
  rw [legMap_involution hr hX, hgr, hgs] at hCrossRight
  rw [hgr, hgs] at hSameRight
  cases l <;> cases k
  · rw [hSame false]
    by_cases hef : e = f <;> simp [signedHalfSource, legSign, nativeHalfX, hef]
  · rw [hCross false true (by decide)]
    simp [signedHalfSource, legSign, nativeHalfX]
  · rw [hCross true false (by decide)]
    simp [signedHalfSource, legSign, nativeHalfX, hCrossRight]
  · rw [hSame true]
    simp only [nativeHalfX, ite_true, hSameRight]
    by_cases hef : e = f <;> simp [signedHalfSource, legSign, hef]

open OriginalFourMActualChart (Chart Puncture parameter scaleRoot localCoordinate
  halfDifferentialAt pullB pullD)
open OriginalFourMPeriodSource (chartCorrection dPeriod)

private def covOnChart (upperA : Bool) (c : Chart) (z x X : ℂ) : ℂ :=
  spatialKernel (1 - parameter c z) x X - chartCorrection upperA c z

/-- The actual A source supplies the left-hand covariance on both chart
overlaps. After restoring the same-puncture term, its discrepancy from
the geometric B or D covariance is the complementary-period product. -/
theorem native_A_covariance_discrepancy (upperA l k e f : Bool) {z : ℝ}
    (hz : 0 < z) (hz1 : z < 1) {q Q w : ℂ}
    (hwA : w ^ 2 = parameter .A (z : ℂ))
    (hu : ‖q ^ 2‖ + ‖w‖ < 1) (hv : ‖Q ^ 2‖ + ‖w‖ < 1)
    (hq : q ≠ 0) (hQ : Q ≠ 0) (hw : w ≠ 0)
    (hg : G e f (q ^ 2) (Q ^ 2) ≠ 0)
    (hx : rightChart e (q ^ 2) - 1 ≠ 0) (hX : rightChart f (Q ^ 2) - 1 ≠ 0)
    (hxx : rightChart e (q ^ 2) - rightChart f (Q ^ 2) ≠ 0)
    (hcross : rightChart e (q ^ 2) - leftChart f (w ^ 2) (Q ^ 2) ≠ 0) :
    let r := w ^ 2
    let u := q ^ 2
    let v := Q ^ 2
    let x := nativeHalfX l e r q
    let X := nativeHalfX k f r Q
    let restored := covarianceMode l k e f u v r +
      (if l = k ∧ e = f then cauchy e f u v else 0)
    let bFactor := (-Complex.I * (Real.sqrt z : ℂ))^2
    let dFactor := Complex.I^2
    let m := signedHalfSource l e u r * signedHalfSource k f v r
    (z * x - 1 ≠ 0) → (z * X - 1 ≠ 0) → (x - X ≠ 0) →
    bFactor * restored - m * covOnChart upperA .B z (pullB z x) (pullB z X) =
      m / ((Real.pi : ℂ) * slitPeriod (1 - (z : ℂ)) * slitPeriod z) ∧
    dFactor * restored - m * covOnChart upperA .D z (pullD z x) (pullD z X) =
      m / ((Real.pi : ℂ) * slitPeriod r * dPeriod upperA (parameter .D z)) := by
  dsimp only
  intro h₁ h₂ h₃
  rw [native_geometric_covariance l k e f hu hv hq hQ hw hg hx hX hxx hcross, hwA]
  obtain ⟨hB, hD⟩ := OriginalFourMPeriodSource.covariance_discrepancies upperA hz hz1 h₁ h₂ h₃
  rw [hwA] at hB hD
  unfold covOnChart
  simp only [chartCorrection, parameter] at hB hD ⊢
  constructor
  · linear_combination (signedHalfSource l e (q ^ 2) (1 - (z : ℂ)⁻¹) *
      signedHalfSource k f (Q ^ 2) (1 - (z : ℂ)⁻¹)) * hB
  · linear_combination (signedHalfSource l e (q ^ 2) (1 - (z : ℂ)⁻¹) *
      signedHalfSource k f (Q ^ 2) (1 - (z : ℂ)⁻¹)) * hD

open OriginalFourMActualChart (periodRoot)
open private leftP leftQ rightS rightSign outgoing from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

private def chartPuncture (c : Chart) (right e : Bool) : Puncture :=
  if right then (if e then .S else rightS c) else (if e then leftQ c else leftP c)

private def normalizedBranch (e : Bool) (u r : ℂ) : ℂ :=
  if e then h e u r / b u else h e u r / (b u * (1 - r))

private def chosenChartSource (c : Chart) (z : ℝ) (e : Bool) (u : ℂ) : ℂ :=
  (1 / (b u * (if e then 1 else periodRoot c z))) *
    normalizedBranch e u (parameter c z) ^ (-1 / 2 : ℂ)

private theorem chart_parameter_ne_one {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) :
    1 - parameter c (z : ℂ) ≠ 0 := by
  have h0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h1 : (z : ℂ) ≠ 1 := by exact_mod_cast hz1.ne
  cases c
  · simpa [parameter] using inv_ne_zero h0
  · exact sub_ne_zero.mpr h1.symm
  · exact sub_ne_zero.mpr (fun h => h1 (inv_eq_one.mp h.symm))

private theorem chartSource_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) (e : Bool) :
    chosenChartSource c z e 0 = (if e then 1 else periodRoot c z)⁻¹ := by
  have hd := chart_parameter_ne_one hz hz1 c
  cases e <;> simp [chosenChartSource, normalizedBranch, h, b, hd]

/-- The selected physical half-coordinate differential at each original
puncture, including the detector, is the oriented source divided by the
chosen root of the physical coordinate derivative. -/
theorem chart_source_at_puncture {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (c : Chart) (right e : Bool) :
    legSign right * chosenChartSource c z e 0 / scaleRoot c z (chartPuncture c right e) =
      halfDifferentialAt c z (chartPuncture c right e) := by
  rw [chartSource_zero hz hz1]
  cases c <;> cases right <;> cases e <;>
    simp [legSign, chartPuncture, leftP, leftQ, rightS, halfDifferentialAt, outgoing,
      rightSign, div_eq_mul_inv, mul_comm]

/-- The physical base-point signs of the actual four source normalizations. -/
theorem chart_chosen_source_signs {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (lA eA lB eB lD eD : Bool)
    (hB : chartPuncture .A lA eA = chartPuncture .B lB eB)
    (hD : chartPuncture .A lA eA = chartPuncture .D lD eD) :
    let M c l e := legSign l * chosenChartSource c z e 0 / scaleRoot c z (chartPuncture c l e)
    M .A lA eA =
      (-Complex.I * (Real.sqrt z : ℂ)) *
        OriginalFourMActualChart.relativeB (chartPuncture .A lA eA) * M .B lB eB ∧
    M .A lA eA =
      Complex.I * OriginalFourMActualChart.relativeD (chartPuncture .A lA eA) * M .D lD eD := by
  dsimp only
  simp only [chart_source_at_puncture hz hz1]
  rw [← hB, ← hD]
  exact OriginalFourMActualChart.half_differential_signs hz hz1 _

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSignedOverlap
