/- GID: D5/S3/Quantum/Recovery/PetzRetainedQubitPairing
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzRetainedQubitPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite retained-qubit blocks share the norms of their noncentral coefficients. -/

import D5.S3.Quantum.Recovery.PetzSupportedLinearRank

/-! Centered logistic estimates for the opposite blocks of the ordinary Petz boundary. -/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators Matrix Matrix.Norms.Frobenius Kronecker
open D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation (mixedBoundary)
open PetzLogisticEvaluation (correlation)
open PetzExponentialBoundaryEvaluation (petzWeight)
open scoped ComplexOrder MatrixOrder

open ExponentialGramWeightedEvaluation (exponentialSum frequency)

open private frobenius_sq from
  D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
open private mixedBoundary_entry mixedFrequency from
  D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
open private gamma_norm_sq integral_logExponentialMode weighted_energy_eq_gram from
  D5.S3.Analytic.PetzLogisticEvaluation

open D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Recovery.PetzSchwarzRecovery (petz_output_support_projection)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport spectralInverseSqrt)
open D5.S3.Quantum.Recovery.PetzSupportedStinespringGram (recoveredState)
open PetzExponentialBoundaryEvaluation (petzWeight petzWeight_pos)


open private diagonalPhase from D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
open private columns columns_isometry columns_support card_positive_eigenvalues
  exists_retainedFirst_stinespring power_zero from
  D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
open private tensorId tensorId_mul tensorId_adjoint dilate sourceRoot referenceRoot
  sourceRoot_selfAdjoint referenceRoot_selfAdjoint outputSourceColumns outputReferenceColumns
  lowerAmplitude upperAmplitude physical_mixed_sq full_logistic_physical
  trace_error_le_boundary power_of_support_left trace_sq_le_of_dilation levelCount_le_card
  output_rank_le from
  D5.S3.Quantum.Recovery.PetzSupportedLinearRank

namespace D5.S3.Quantum.Recovery.PetzRetainedQubitPairing

local notation "d" => (Real.sqrt 2 / 2)
local notation "λ₀" => (1 + Real.sqrt 2 / 2)

private theorem root_bounds : (7 / 10 : ℝ) < d ∧ d < 1 := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

private def diagonal (x : ℝ) : ℝ := d + 2 * x - (λ₀ + 1) * x ^ 2

private def cross (x y z : ℝ) : ℝ := λ₀ * z - 1 + x + y - (λ₀ + 1) * x * y

private theorem centered_determinant {x y z η : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 5) (hy : 0 ≤ y) (hy' : y ≤ 1 / 5)
    (hz : 0 ≤ z) (hz' : z ≤ 1) (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hshape : η * (1 - z / 2) ≤ d)
    (hgap : (x - y) ^ 2 ≤ (7 / 25) * (1 - z)) :
    0 ≤ diagonal x ∧ 0 ≤ diagonal y ∧ η ^ 2 * cross x y z ^ 2 ≤ diagonal x * diagonal y := by
  have hLambda : λ₀ < 2 := by linarith [root_bounds.2]
  have hLambda_nonneg : 0 ≤ λ₀ := by linarith [root_bounds.1]
  have hfirst {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 5) : d ≤ diagonal t := by
    unfold diagonal
    have hm : (λ₀ + 1) * t ≤ 3 * (1 / 5 : ℝ) :=
      mul_le_mul (by linarith) ht' ht (by norm_num)
    nlinarith [mul_nonneg ht (show 0 ≤ 2 - (λ₀ + 1) * t by linarith)]
  have ha := hfirst hx hx'
  have hb := hfirst hy hy'
  have hd : 0 ≤ d := by linarith [root_bounds.1]
  refine ⟨hd.trans ha, hd.trans hb, ?_⟩
  have hxy : 0 ≤ x + y - (λ₀ + 1) * x * y := by
    have hm : (λ₀ + 1) * x ≤ 3 * (1 / 5 : ℝ) :=
      mul_le_mul (by linarith) hx' hx (by norm_num)
    nlinarith [mul_nonneg hy (show 0 ≤ 1 - (λ₀ + 1) * x by linarith)]
  rcases le_total (cross x y z) 0 with hc | hc
  · have hB : -(cross x y z) ≤ 1 - z / 2 := by
      unfold cross
      nlinarith [mul_nonneg hz (show 0 ≤ λ₀ - 1 / 2 by linarith [root_bounds.1])]
    have ηB : η * -(cross x y z) ≤ d :=
      (mul_le_mul_of_nonneg_left hB hη).trans hshape
    calc
      _ = (η * -(cross x y z)) ^ 2 := by ring
      _ ≤ d ^ 2 := pow_le_pow_left₀ (mul_nonneg hη (neg_nonneg.mpr hc)) ηB 2
      _ ≤ _ := by
        rw [sq]
        exact mul_le_mul ha hb hd (hd.trans ha)
  · let B₁ := cross x y 1
    have hB₁ : d ≤ B₁ := by
      dsimp [B₁, cross]
      linarith
    have hdiff : B₁ - cross x y z = λ₀ * (1 - z) := by dsimp [B₁, cross]; ring
    have hidentity : diagonal x * diagonal y - B₁ ^ 2 = -λ₀ ^ 2 * (x - y) ^ 2 := by
      dsimp [B₁, diagonal, cross]
      generalize Real.sqrt (2 : ℝ) = t
      ring
    have hthreshold : λ₀ * (7 / 25 : ℝ) ≤ d := by linarith [root_bounds.1]
    have hmul : λ₀ ^ 2 * (x - y) ^ 2 ≤
        (λ₀ * (1 - z)) * (B₁ + cross x y z) := calc
      _ ≤ λ₀ ^ 2 * ((7 / 25) * (1 - z)) :=
        mul_le_mul_of_nonneg_left hgap (sq_nonneg _)
      _ = (λ₀ * (1 - z)) * (λ₀ * (7 / 25)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg hLambda_nonneg (sub_nonneg.mpr hz'))
    have hsq : cross x y z ^ 2 ≤ diagonal x * diagonal y := by
      rw [← hdiff] at hmul
      nlinarith only [hmul, hidentity]
    calc
      _ ≤ 1 ^ 2 * cross x y z ^ 2 := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hη hη' 2) (sq_nonneg _)
      _ = cross x y z ^ 2 := by ring
      _ ≤ _ := hsq

private theorem centered_quadratic {x y z η u v r : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 5) (hy : 0 ≤ y) (hy' : y ≤ 1 / 5)
    (hz : 0 ≤ z) (hz' : z ≤ 1) (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hshape : η * (1 - z / 2) ≤ d)
    (hgap : (x - y) ^ 2 ≤ (7 / 25) * (1 - z))
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : |r| ≤ η * (u * v)) :
    (1 - x) ^ 2 * u ^ 2 + (1 - y) ^ 2 * v ^ 2 + 2 * (1 - x) * (1 - y) * r ≤
      λ₀ * ((1 - x ^ 2) * u ^ 2 + (1 - y ^ 2) * v ^ 2 + 2 * (z - x * y) * r) := by
  obtain ⟨ha, hb, hab⟩ := centered_determinant hx hx' hy hy' hz hz' hη hη' hshape hgap
  let A := diagonal x
  let B := diagonal y
  let C := cross x y z
  have hroots : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hcoef : η * |C| ≤ Real.sqrt A * Real.sqrt B := by
    have hs : (η * |C|) ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
      rw [hroots, mul_pow, sq_abs]
      exact hab
    exact (sq_le_sq₀ (mul_nonneg hη (abs_nonneg _)) (by positivity)).mp hs
  have hpair : -(C * r) ≤ (Real.sqrt A * Real.sqrt B) * (u * v) := calc
    _ ≤ |C * r| := neg_le_abs _
    _ = |C| * |r| := abs_mul _ _
    _ ≤ |C| * (η * (u * v)) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
    _ = (η * |C|) * (u * v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hu hv)
  have hq : 0 ≤ A * u ^ 2 + B * v ^ 2 + 2 * C * r := by
    have hsq : (Real.sqrt A * u - Real.sqrt B * v) ^ 2 =
        A * u ^ 2 + B * v ^ 2 - 2 * (Real.sqrt A * Real.sqrt B) * (u * v) := by
      rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
      ring
    nlinarith only [hpair, hsq, sq_nonneg (Real.sqrt A * u - Real.sqrt B * v)]
  dsimp [A, B, C, diagonal, cross] at hq
  linarith only [hq]

/-- Fourier correlation of the probability weight on the upper Petz strip boundary. -/
def logisticCorrelation (t : ℝ) : ℝ :=
  if t = 0 then 1 else (t / 2) / Real.sinh (t / 2)

local notation "logistic" => logisticCorrelation

private theorem logistic_neg (t : ℝ) : logistic (-t) = logistic t := by
  simp only [logisticCorrelation, neg_eq_zero, neg_div, Real.sinh_neg, div_neg, neg_neg]

private theorem logistic_bounds (t : ℝ) : 0 ≤ logistic t ∧ logistic t ≤ 1 := by
  suffices h : ∀ s ≥ (0 : ℝ), 0 ≤ logistic s ∧ logistic s ≤ 1 by
    rcases le_total 0 t with ht | ht
    · exact h t ht
    · rw [← logistic_neg]
      exact h (-t) (neg_nonneg.mpr ht)
  intro s hs
  rcases eq_or_lt_of_le hs with rfl | hs
  · norm_num [logisticCorrelation]
  have hhalf : 0 < s / 2 := by positivity
  have hden := Real.sinh_pos_iff.mpr hhalf
  rw [logisticCorrelation, ite_eq_right hs.ne']
  exact ⟨div_nonneg hhalf.le hden.le, (div_le_one₀ hden).2
    (Real.self_le_sinh_iff.mpr hhalf.le)⟩

private theorem mul_cosh_sub_sinh_monotone :
    MonotoneOn (fun u : ℝ => u * Real.cosh u - Real.sinh u) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by fun_prop)
    · intro x _
      exact (((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
        (Real.hasDerivAt_sinh x)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 ≤ x := interior_subset hx
      change 0 ≤ deriv (id * Real.cosh - Real.sinh) x
      rw [(((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
        (Real.hasDerivAt_sinh x)).deriv]
      simp only [id_eq, one_mul, add_sub_cancel_left]
      exact mul_nonneg hx' (Real.sinh_nonneg_iff.mpr hx')

private theorem logistic_ge_sech_sq (t : ℝ) : 1 / Real.cosh (t / 4) ^ 2 ≤ logistic t := by
  have hmon := mul_cosh_sub_sinh_monotone
  suffices h : ∀ s ≥ (0 : ℝ), 1 / Real.cosh (s / 4) ^ 2 ≤ logistic s by
    rcases le_total 0 t with ht | ht
    · exact h t ht
    · simpa only [neg_div, Real.cosh_neg, logistic_neg] using h (-t) (neg_nonneg.mpr ht)
  intro s hs
  rcases eq_or_lt_of_le hs with rfl | hs
  · norm_num [logisticCorrelation]
  let u := s / 4
  have hu : 0 < u := by positivity
  have hc := Real.cosh_pos u
  have hval : Real.sinh u ≤ u * Real.cosh u := by
    have h := hmon (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp) hu.le hu.le
    simpa only [zero_mul, Real.sinh_zero, sub_zero, sub_nonneg] using h
  have hu₂ : s / 2 = 2 * u := by dsimp [u]; ring
  rw [logisticCorrelation, ite_eq_right hs.ne', hu₂, Real.sinh_two_mul]
  change 1 / Real.cosh u ^ 2 ≤ 2 * u / (2 * Real.sinh u * Real.cosh u)
  have hden : 0 < 2 * Real.sinh u * Real.cosh u := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hc) hden).2
  nlinarith only [mul_le_mul_of_nonneg_right hval (show 0 ≤ 2 * Real.cosh u by positivity)]

private theorem logistic_correlation {ι : Type*} (ω : ι → ℝ) (i j : ι) :
    (‖correlation ω i j‖ ^ 2 : ℂ) = (logistic (ω j - ω i) : ℂ) := by
  rw [correlation, Matrix.of_apply, integral_logExponentialMode]
  exact gamma_norm_sq _

private theorem logistic_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt logistic
      ((Real.sinh (x / 2) - (x / 2) * Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2) ^ 2)) x := by
  have ht : 0 < x / 2 := by positivity
  have hs := (Real.sinh_pos_iff.mpr ht).ne'
  have h₁ : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
  have h := h₁.div (h₁.sinh) hs
  change HasDerivAt (fun t : ℝ => (t/2) / Real.sinh (t/2)) _ x at h
  have heq : logistic =ᶠ[nhds x] (fun t : ℝ => (t / 2) / Real.sinh (t / 2)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact ite_eq_right (Set.mem_Ioi.mp ht).ne'
  convert h.congr_of_eventuallyEq heq using 1
  ring

private theorem logistic_slope {x : ℝ} (hx : 0 < x) :
    -(logistic x) / 2 ≤ deriv logistic x ∧ deriv logistic x ≤ 0 := by
  let t := x / 2
  have ht : 0 < t := by positivity
  have hs := Real.sinh_pos_iff.mpr ht
  have hc := Real.cosh_pos t
  rw [(logistic_derivative hx).deriv, logisticCorrelation, ite_eq_right hx.ne']
  change -(t / Real.sinh t) / 2 ≤
      (Real.sinh t - t * Real.cosh t) / (2 * Real.sinh t ^ 2) ∧
    (Real.sinh t - t * Real.cosh t) / (2 * Real.sinh t ^ 2) ≤ 0
  have hden : 0 < 2 * Real.sinh t ^ 2 := by positivity
  constructor
  · have hexp : t * Real.exp (-t) ≤ Real.sinh t := by
      have hE := Real.add_one_le_exp (2 * t)
      have h := mul_le_mul_of_nonneg_right hE (Real.exp_pos (-t)).le
      rw [← Real.exp_add, show 2*t + -t = t by ring] at h
      rw [Real.sinh_eq]
      linarith only [h]
    apply (le_div_iff₀ hden).2
    have hcancel : -(t / Real.sinh t) / 2 * (2 * Real.sinh t ^ 2) =
        -t * Real.sinh t := by field_simp [hs.ne']
    rw [hcancel]
    have hh := Real.cosh_sub_sinh t
    nlinarith only [hexp, mul_nonneg ht.le (sub_nonneg.mpr hh.le),
      mul_nonneg ht.le (sub_nonneg.mpr hh.ge)]
  · apply div_nonpos_of_nonpos_of_nonneg _ hden.le
    have hmon := mul_cosh_sub_sinh_monotone
    have h := hmon (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp) ht.le ht.le
    simp only [zero_mul, Real.sinh_zero, sub_zero] at h
    linarith only [h]

private theorem logistic_le_cubic (s : ℝ) :
    s ^ 2 ≤ (24 + s ^ 2) * (1 - logistic s) := by
  have hSinh {x : ℝ} (hx : 0 ≤ x) : x + x ^ 3 / 6 ≤ Real.sinh x := by
    have hD (v : ℝ) : HasDerivAt (fun u : ℝ => Real.sinh u - (u + u ^ 3 / 6))
        (Real.cosh v - (1 + v ^ 2 / 2)) v := by
      convert (Real.hasDerivAt_sinh v).sub ((hasDerivAt_id v).add
        (((hasDerivAt_id v).pow 3).div_const 6)) using 1
      · ext u
        rfl
      · norm_num
        ring
    have hM : MonotoneOn (fun u : ℝ => Real.sinh u - (u + u ^ 3 / 6)) (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici _) (by fun_prop)
        (fun u _ => (hD u).differentiableAt.differentiableWithinAt) ?_
      intro u hu
      have hu' : 0 ≤ u := interior_subset hu
      have hu2 : 0 ≤ u / 2 := by positivity
      have hsq := pow_le_pow_left₀ hu2 (Real.self_le_sinh_iff.mpr hu2) 2
      rw [(hD u).deriv, show u = 2 * (u / 2) by ring, Real.cosh_two_mul]
      linarith only [Real.cosh_sq_sub_sinh_sq (u / 2), hsq]
    have h := hM (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp) hx hx
    simpa only [Real.sinh_zero, zero_pow (by decide : (3:ℕ) ≠ 0), zero_div, add_zero, sub_zero,
      sub_nonneg] using h
  have hAux (t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ (24 + t ^ 2) * (1 - logistic t) := by
    rcases eq_or_lt_of_le ht with rfl | ht'
    · norm_num [logisticCorrelation]
    have hpos : 0 < t / 2 := by positivity
    have hs := Real.sinh_pos_iff.mpr hpos
    rw [logisticCorrelation, ite_eq_right ht'.ne']
    have h := hSinh hpos.le
    have hcal : (24 + t ^ 2) * ((t / 2) / Real.sinh (t / 2)) ≤ 24 := by
      rw [← mul_div_assoc, div_le_iff₀ hs]
      linarith only [h]
    linarith only [hcal]
  rcases le_total 0 s with hs | hs
  · exact hAux s hs
  · simpa only [neg_sq, logistic_neg] using hAux (-s) (neg_nonneg.mpr hs)

private theorem logistic_gap (a b : ℝ)
    (ha : logistic a ≤ 1 / 5) (hb : logistic b ≤ 1 / 5) :
    (logistic a - logistic b) ^ 2 ≤ (7 / 25) * (1 - logistic (a - b)) := by
  have hAbs (x : ℝ) : logistic |x| = logistic x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, logistic_neg]
  have hmono : AntitoneOn logistic (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _) ?_ ?_ ?_
    · exact (fun u hu => (logistic_derivative hu).continuousAt.continuousWithinAt)
    · intro u hu
      exact (logistic_derivative (interior_subset hu)).differentiableAt.differentiableWithinAt
    · exact fun u hu => (logistic_slope (interior_subset hu)).2
  have hna (x : ℝ) (hx : logistic x ≤ 1 / 5) : 0 < |x| := by
    apply abs_pos.mpr
    rintro rfl
    norm_num [logisticCorrelation] at hx
  have hf (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hsmall : logistic x ≤ 1 / 5) :
      |logistic y - logistic x| ≤ (1 / 10) * |y - x| := by
    have hu (t : ℝ) (ht : t ∈ Set.Icc x y) : 0 < t := hx.trans_le ht.1
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
      (fun t ht => (logistic_derivative (hu t ht)).differentiableAt)
      (fun t ht => show ‖deriv logistic t‖ ≤ (1 / 10 : ℝ) by
        have htSmall := (hmono hx (hu t ht) ht.1).trans hsmall
        obtain ⟨hl, hr⟩ := logistic_slope (hu t ht)
        rw [Real.norm_eq_abs, abs_of_nonpos hr]
        linarith)
      (convex_Icc x y) (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy)
    simpa only [Real.norm_eq_abs] using h
  have hh : |logistic a - logistic b| ≤ (1 / 10) * |a - b| := by
    have hdist := abs_abs_sub_abs_le_abs_sub a b
    rcases le_total |a| |b| with hab | hba
    · have h := hf |a| |b| (hna a ha) hab (by rwa [hAbs])
      rw [hAbs, hAbs, abs_sub_comm (logistic b), abs_sub_comm |b|] at h
      exact h.trans (mul_le_mul_of_nonneg_left hdist (by norm_num))
    · have h := hf |b| |a| (hna b hb) hba (by rwa [hAbs])
      rw [hAbs, hAbs] at h
      exact h.trans (mul_le_mul_of_nonneg_left hdist (by norm_num))
  have habs : |logistic a - logistic b| ≤ 1 / 5 := by
    rw [abs_le]
    exact ⟨by linarith [(logistic_bounds a).1], by linarith [(logistic_bounds b).1]⟩
  have hs := logistic_le_cubic (a - b)
  have hz := (logistic_bounds (a - b)).2
  by_cases ht : |a - b| ≤ 2
  · have hs' := pow_le_pow_left₀ (abs_nonneg (a-b)) ht 2
    rw [sq_abs] at hs'
    have hcoef : (a - b)^2 ≤ 28 * (1 - logistic (a - b)) :=
      hs.trans (mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hz))
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [mul_pow, sq_abs, sq_abs] at hsq
    linarith only [hsq, hcoef]
  · have hs' := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) (le_of_not_ge ht) 2
    rw [sq_abs] at hs'
    have hm : (24 + (a-b)^2) * (1 / 7) ≤ (a-b)^2 := by linarith
    have hpos : 0 < 24 + (a-b)^2 := by positivity
    have hz' := (mul_le_mul_iff_right₀ hpos).mp (hm.trans hs)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    linarith only [hz', hsq]


section Blocks

variable {e : Type*} [Fintype e]

private abbrev Qubit := Fin 2

private def block (X : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) :
    Matrix e e ℂ := fun u v => X (i, u) (j, v)

omit [Fintype e] in
private theorem block_adjoint {X : Matrix (Qubit × e) (Qubit × e) ℂ}
    (hX : X.IsHermitian) (i j : Qubit) : (block X i j)ᴴ = block X j i := by
  ext u v
  exact congrFun (congrFun hX.eq (j, u)) (i, v)

private theorem opposite_norm {U : Matrix Qubit Qubit ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (i j : Qubit) :
    ‖U i j‖ = ‖U i.rev j.rev‖ := by
  have hrow (i : Qubit) : ‖U i 0‖ ^ 2 + ‖U i 1‖ ^ 2 = 1 := by
    have h := congrArg Complex.re (congrFun (congrFun hU' i) i)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply_eq, Complex.add_re, RCLike.star_def, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq, Complex.one_re] using h
  have hcol (j : Qubit) : ‖U 0 j‖ ^ 2 + ‖U 1 j‖ ^ 2 = 1 := by
    have h := congrArg Complex.re (congrFun (congrFun hU j) j)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply_eq, Complex.add_re, RCLike.star_def, Complex.conj_mul',
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] using h
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  fin_cases i <;> fin_cases j
  · change ‖U 0 0‖ ^ 2 = ‖U 1 1‖ ^ 2
    linarith only [hrow 0, hcol 1]
  · change ‖U 0 1‖ ^ 2 = ‖U 1 0‖ ^ 2
    linarith only [hrow 0, hcol 0]
  · change ‖U 1 0‖ ^ 2 = ‖U 0 1‖ ^ 2
    linarith only [hrow 0, hcol 0]
  · change ‖U 1 1‖ ^ 2 = ‖U 0 0‖ ^ 2
    linarith only [hrow 0, hcol 1]

private def innerRe (A B : Matrix e e ℂ) : ℝ :=
  ∑ u, ∑ v, (star (A u v) * B u v).re

private theorem abs_innerRe_le (A B : Matrix e e ℂ) : |innerRe A B| ≤ ‖A‖ * ‖B‖ := by
  let a (uv : e × e) := ‖A uv.1 uv.2‖
  let b (uv : e × e) := ‖B uv.1 uv.2‖
  have ha : (∑ uv, a uv ^ 2) = ‖A‖ ^ 2 := by
    rw [frobenius_sq, Fintype.sum_prod_type]
  have hb : (∑ uv, b uv ^ 2) = ‖B‖ ^ 2 := by
    rw [frobenius_sq, Fintype.sum_prod_type]
  have hn : (∑ uv, a uv * b uv) ≤ ‖A‖ * ‖B‖ := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun uv _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, ← ha, ← hb]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ a b
  have hentry (uv : e × e) :
      |(star (A uv.1 uv.2) * B uv.1 uv.2).re| ≤ a uv * b uv := by
    refine (Complex.abs_re_le_norm _).trans_eq ?_
    simp [a, b]
  unfold innerRe
  rw [← Fintype.sum_prod_type (f := fun uv : e × e => (star (A uv.1 uv.2) * B uv.1 uv.2).re)]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun uv _ => hentry uv).trans hn)

private def halfRatio (p q : ℝ) : ℝ := Real.exp ((Real.log p - Real.log q) / 2)

private def pairedAngle (h k : ℝ) : ℝ := (h + k) / Real.sqrt (2 * (h ^ 2 + k ^ 2))

private theorem pairedAngle_bounds {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    0 ≤ pairedAngle h k ∧ pairedAngle h k ≤ 1 ∧
      pairedAngle h k * (1 - (4 * h * k / (h + k) ^ 2) / 2) ≤ d := by
  have hd₀ : 0 ≤ d := by linarith [root_bounds.1]
  have hd₂ : d ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsum : 0 < h + k := add_pos hh hk
  have hss : 0 < h ^ 2 + k ^ 2 := by positivity
  have hden : 0 < Real.sqrt (2 * (h ^ 2 + k ^ 2)) := Real.sqrt_pos.2 (by positivity)
  have hden₂ := Real.sq_sqrt (show 0 ≤ 2 * (h ^ 2 + k ^ 2) by positivity)
  have hprod : 0 ≤ h * k := mul_nonneg hh.le hk.le
  refine ⟨div_nonneg hsum.le hden.le, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    rw [one_mul]
    apply (sq_le_sq₀ hsum.le hden.le).mp
    rw [hden₂]
    nlinarith only [sq_nonneg (h-k)]
  · have hid : 1 - (4 * h * k / (h + k) ^ 2) / 2 =
        (h ^ 2 + k ^ 2) / (h + k) ^ 2 := by
      field_simp [hsum.ne']
      ring
    have hcancel : pairedAngle h k * ((h ^ 2 + k ^ 2) / (h + k) ^ 2) =
        (h ^ 2 + k ^ 2) / (Real.sqrt (2 * (h ^ 2 + k ^ 2)) * (h + k)) := by
      unfold pairedAngle
      field_simp [hsum.ne', hden.ne']
    rw [hid, hcancel]
    apply (div_le_iff₀ (mul_pos hden hsum)).2
    apply (sq_le_sq₀ hss.le (mul_nonneg hd₀ (mul_nonneg hden.le hsum.le))).mp
    rw [mul_pow, mul_pow, hd₂, hden₂]
    nlinarith only [mul_nonneg hss.le (show 0 ≤ (h + k) ^ 2 - (h ^ 2 + k ^ 2) by
      nlinarith only [hprod])]

private theorem halfRatio_shape (a b c f : ℝ) :
    4 * halfRatio a b * halfRatio c f / (halfRatio a b + halfRatio c f) ^ 2 =
      1 / Real.cosh (((Real.log c - Real.log a) - (Real.log f - Real.log b)) / 4) ^ 2 := by
  let x := Real.log a - Real.log b
  let y := Real.log c - Real.log f
  have hxy : (Real.log c - Real.log a) - (Real.log f - Real.log b) = y - x := by
    dsimp [x, y]
    ring
  rw [hxy]
  change 4 * Real.exp (x / 2) * Real.exp (y / 2) /
    (Real.exp (x / 2) + Real.exp (y / 2)) ^ 2 = _
  let m := Real.exp ((x + y) / 4)
  have hm : 0 < m := Real.exp_pos _
  have hpos : Real.exp (x / 2) + Real.exp (y / 2) = 2 * m * Real.cosh ((y-x)/4) := by
    rw [Real.cosh_eq]
    calc
      _ = m * Real.exp ((y - x) / 4) + m * Real.exp (-((y - x) / 4)) := by
        dsimp [m]
        rw [← Real.exp_add, ← Real.exp_add, show (x+y)/4 + (y-x)/4 = y/2 by ring,
          show (x+y)/4 + -((y-x)/4) = x/2 by ring]
        ring
      _ = _ := by ring
  have hprod : Real.exp (x / 2) * Real.exp (y / 2) = m ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    dsimp [m]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpos, mul_assoc 4, hprod]
  have hc := (Real.cosh_pos ((y-x)/4)).ne'
  field_simp [hm.ne', hc]
  ring

private def sourceOff (U : Matrix Qubit Qubit ℂ) (X : Matrix (Qubit × e) (Qubit × e) ℂ)
    (i j : Qubit) : Matrix e e ℂ := U i j.rev • block X j.rev j

private def referenceOff (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) : Matrix e e ℂ :=
  (-(halfRatio (p j) (q i.rev) : ℂ) * U i.rev j) • block Y i i.rev

private theorem paired_inner_bound (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (i j : Qubit) :
    let A := sourceOff U X i j
    let A' := sourceOff U X i.rev j.rev
    let B := referenceOff p q U Y i j
    let B' := referenceOff p q U Y i.rev j.rev
    let h := halfRatio (p j) (q i.rev)
    let k := halfRatio (p j.rev) (q i)
    |innerRe A B + innerRe A' B'| ≤ pairedAngle h k *
      (Real.sqrt (‖A‖ ^ 2 + ‖A'‖ ^ 2) * Real.sqrt (‖B‖ ^ 2 + ‖B'‖ ^ 2)) := by
  dsimp only
  let m := ‖U i j.rev‖
  let h := halfRatio (p j) (q i.rev)
  let k := halfRatio (p j.rev) (q i)
  let a := m * ‖block X j.rev j‖
  let b := m * ‖block Y i i.rev‖
  have hh : 0 < h := Real.exp_pos _
  have hk : 0 < k := Real.exp_pos _
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hOpp := opposite_norm hU hU' i j.rev
  rw [Fin.rev_rev] at hOpp
  have hA : ‖sourceOff U X i j‖ = a := by simp [sourceOff, a, m, norm_smul]
  have hA' : ‖sourceOff U X i.rev j.rev‖ = a := by
    rw [sourceOff, norm_smul, Fin.rev_rev, ← hOpp, ← block_adjoint hX j.rev j,
      Matrix.frobenius_norm_conjTranspose]
  have hB : ‖referenceOff p q U Y i j‖ = h * b := by
    rw [referenceOff, norm_smul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh, ← hOpp]
    ring
  have hB' : ‖referenceOff p q U Y i.rev j.rev‖ = k * b := by
    rw [referenceOff, Fin.rev_rev, norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hk, ← block_adjoint hY i i.rev,
      Matrix.frobenius_norm_conjTranspose]
    ring
  have hscale : (h + k) * a * b = pairedAngle h k *
      (Real.sqrt (a ^ 2 + a ^ 2) * Real.sqrt ((h * b) ^ 2 + (k * b) ^ 2)) := by
    have h₂ : 0 ≤ (2 : ℝ) := by norm_num
    have hs : 0 ≤ h ^ 2 + k ^ 2 := by positivity
    rw [show a ^ 2 + a ^ 2 = 2 * a ^ 2 by ring,
      show (h * b) ^ 2 + (k * b) ^ 2 = (h ^ 2 + k ^ 2) * b ^ 2 by ring,
      Real.sqrt_mul h₂, Real.sqrt_mul hs, Real.sqrt_sq ha, Real.sqrt_sq hb,
      pairedAngle, Real.sqrt_mul h₂]
    have hp : Real.sqrt 2 * Real.sqrt (h ^ 2 + k ^ 2) ≠ 0 := by positivity
    field_simp [hp]
  calc
    _ ≤ |innerRe (sourceOff U X i j) (referenceOff p q U Y i j)| +
        |innerRe (sourceOff U X i.rev j.rev) (referenceOff p q U Y i.rev j.rev)| := abs_add_le _ _
    _ ≤ ‖sourceOff U X i j‖ * ‖referenceOff p q U Y i j‖ +
        ‖sourceOff U X i.rev j.rev‖ * ‖referenceOff p q U Y i.rev j.rev‖ :=
      add_le_add (abs_innerRe_le _ _) (abs_innerRe_le _ _)
    _ = _ := by
      rw [hA, hA', hB, hB', ← hscale]
      ring

private def sourceGap (p : Qubit → ℝ) (j : Qubit) : ℝ :=
  Real.log (p j.rev) - Real.log (p j)

private def referenceGap (q : Qubit → ℝ) (i : Qubit) : ℝ :=
  Real.log (q i) - Real.log (q i.rev)

private theorem pair_shape (p q : Qubit → ℝ) (i j : Qubit) :
    let h := halfRatio (p j) (q i.rev)
    let k := halfRatio (p j.rev) (q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    pairedAngle h k * (1 - z / 2) ≤ d := by
  dsimp only
  let h := halfRatio (p j) (q i.rev)
  let k := halfRatio (p j.rev) (q i)
  have hh : 0 < h := Real.exp_pos _
  have hk : 0 < k := Real.exp_pos _
  have hsech := halfRatio_shape (p j) (q i.rev) (p j.rev) (q i)
  have hz := logistic_ge_sech_sq (sourceGap p j - referenceGap q i)
  have hz' : 4 * h * k / (h + k) ^ 2 ≤ logistic (sourceGap p j - referenceGap q i) := by
    exact hsech.le.trans hz
  obtain ⟨h₀, _, hb⟩ := pairedAngle_bounds hh hk
  exact (mul_le_mul_of_nonneg_left (by linarith only [hz']) h₀).trans hb

private def centeredEndpoint (x y : ℝ) (A B : Matrix e e ℂ) : Matrix e e ℂ :=
  (1 - (x : ℂ)) • A + (1 - (y : ℂ)) • B

private theorem norm_centeredEndpoint (x y : ℝ) (A B : Matrix e e ℂ) :
    ‖centeredEndpoint x y A B‖ ^ 2 =
      (1-x)^2 * ‖A‖^2 + (1-y)^2 * ‖B‖^2 + 2*(1-x)*(1-y)*innerRe A B := by
  simp only [centeredEndpoint, innerRe, frobenius_sq]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.sq_norm,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private def centeredEnergy (x y z : ℝ) (A B : Matrix e e ℂ) : ℝ :=
  (1 - x ^ 2) * ‖A‖ ^ 2 + (1 - y ^ 2) * ‖B‖ ^ 2 + 2 * (z - x * y) * innerRe A B

private theorem physical_centered_pair (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (i j : Qubit)
    (hx : logistic (sourceGap p j) ≤ 1 / 5) (hy : logistic (referenceGap q i) ≤ 1 / 5)
    (hgap : (logistic (sourceGap p j) - logistic (referenceGap q i)) ^ 2 ≤
      (7 / 25) * (1 - logistic (sourceGap p j - referenceGap q i))) :
    let x := logistic (sourceGap p j)
    let y := logistic (referenceGap q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    let A := sourceOff U X i j
    let A' := sourceOff U X i.rev j.rev
    let B := referenceOff p q U Y i j
    let B' := referenceOff p q U Y i.rev j.rev
    ‖centeredEndpoint x y A B‖ ^ 2 + ‖centeredEndpoint x y A' B'‖ ^ 2 ≤
      λ₀ * (centeredEnergy x y z A B + centeredEnergy x y z A' B') := by
  dsimp only
  let x := logistic (sourceGap p j)
  let y := logistic (referenceGap q i)
  let z := logistic (sourceGap p j - referenceGap q i)
  let A := sourceOff U X i j
  let A' := sourceOff U X i.rev j.rev
  let B := referenceOff p q U Y i j
  let B' := referenceOff p q U Y i.rev j.rev
  let h := halfRatio (p j) (q i.rev)
  let k := halfRatio (p j.rev) (q i)
  change ‖centeredEndpoint x y A B‖ ^ 2 + ‖centeredEndpoint x y A' B'‖ ^ 2 ≤
    λ₀ * (centeredEnergy x y z A B + centeredEnergy x y z A' B')
  have hpair : |innerRe A B + innerRe A' B'| ≤ pairedAngle h k *
      (Real.sqrt (‖A‖ ^ 2 + ‖A'‖ ^ 2) * Real.sqrt (‖B‖ ^ 2 + ‖B'‖ ^ 2)) :=
    paired_inner_bound p q U hU hU' X Y hX hY i j
  have hang := pairedAngle_bounds (show 0 < h from Real.exp_pos _) (show 0 < k from Real.exp_pos _)
  have hz := logistic_bounds (sourceGap p j - referenceGap q i)
  have hresult := centered_quadratic (logistic_bounds (sourceGap p j)).1 hx
    (logistic_bounds (referenceGap q i)).1 hy hz.1 hz.2 hang.1 hang.2.1
    (pair_shape p q i j) hgap (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hpair
  change _ ≤ λ₀ * ((1-x^2) * _ + (1-y^2) * _ + 2*(z-x*y)*_) at hresult
  rw [Real.sq_sqrt (by positivity : 0 ≤ ‖A‖ ^ 2 + ‖A'‖ ^ 2),
    Real.sq_sqrt (by positivity : 0 ≤ ‖B‖ ^ 2 + ‖B'‖ ^ 2)] at hresult
  rw [norm_centeredEndpoint, norm_centeredEndpoint]
  unfold centeredEnergy
  linarith only [hresult]

private def central (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) : Matrix e e ℂ :=
  U i j • block X j j - ((halfRatio (p j) (q i) : ℂ) * U i j) • block Y i i

private theorem sum_qubit {R : Type*} [AddCommMonoid R] (a : Qubit → R) (i : Qubit) :
    (∑ k, a k) = a i + a i.rev := by
  rw [Fin.sum_univ_two]
  fin_cases i
  · rfl
  · exact add_comm _ _

omit [Fintype e] in
private theorem ofReal_halfRatio (p q : ℝ) :
    (halfRatio p q : ℂ) =
      Complex.exp ((Real.log p : ℂ) * ((1 / 2 : ℝ) : ℂ) -
        (Real.log q : ℂ) * ((1 / 2 : ℝ) : ℂ)) := by
  rw [halfRatio, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem mixedBoundary_qubit_entry [DecidableEq e]
    (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) (u v : e) (t : ℝ) :
    mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v) =
      Complex.exp (frequency (fun _ : Unit => Real.log (p j) - Real.log (q i)) () * (t : ℂ)) *
        exponentialSum ![0, sourceGap p j, referenceGap q i]
          ![central p q U X Y i j u v, sourceOff U X i j u v, referenceOff p q U Y i j u v]
          (t : ℂ) := by
  rw [mixedBoundary_entry]
  have hX (k : Qubit) : (∑ w : e, (U ⊗ₖ (1 : Matrix e e ℂ)) (i,u) (k,w) *
      X (k,w) (j,v)) = U i k * X (k,u) (j,v) := by
    simp only [Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hw
      simp [Ne.symm hw]
    · simp
  have hY (k : Qubit) : (∑ w : e, Y (i,u) (k,w) *
      (U ⊗ₖ (1 : Matrix e e ℂ)) (k,w) (j,v)) = Y (i,u) (k,v) * U k j := by
    simp only [Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      simp [hw]
    · simp
  have hPhase (a b : ℝ) :
      Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) *
        Complex.exp (Complex.I * (b : ℂ) * (t : ℂ)) =
      Complex.exp (Complex.I * ((a + b : ℝ) : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    push_cast
    congr 1
    ring
  simp only [exponentialSum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    mixedFrequency, frequency, hX, hY, ← ofReal_halfRatio, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.exp_zero, mul_one]
  rw [sum_qubit _ j, sum_qubit _ i]
  simp only [central, sourceOff, referenceOff, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    block, mul_add, mul_sub]
  have hA : Real.log (p j) - Real.log (q i) + sourceGap p j =
      Real.log (p j.rev) - Real.log (q i) := by unfold sourceGap; ring
  have hB : Real.log (p j) - Real.log (q i) + referenceGap q i =
      Real.log (p j) - Real.log (q i.rev) := by unfold referenceGap; ring
  rw [← hA, ← hB, ← hPhase, ← hPhase]
  ring

private theorem scalar_energy (α β : ℝ) (C A B : ℂ) :
    let F (t : ℝ) := exponentialSum ![0, α, β] ![C, A, B] (t : ℂ)
    let x := logistic α
    let y := logistic β
    let z := logistic (α - β)
    Integrable (fun t => petzWeight t * ‖F t‖ ^ 2) ∧
    (∫ t, petzWeight t * ‖F t‖ ^ 2) =
      ‖C + (x : ℂ) * A + (y : ℂ) * B‖ ^ 2 +
        ((1-x^2)*‖A‖^2 + (1-y^2)*‖B‖^2 + 2*(z-x*y)*(star A*B).re) := by
  dsimp only
  obtain ⟨hInt, he⟩ := weighted_energy_eq_gram (![0, α, β] : Fin 3 → ℝ) (![C,A,B] : Fin 3 → ℂ)
  refine ⟨hInt, ?_⟩
  simp only [logistic_correlation] at he
  have h := congrArg Complex.re he
  simp only [Complex.ofReal_re, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl, sub_zero, zero_sub, sub_self, logistic_neg,
    show β - α = -(α - β) by ring,
    show logistic 0 = 1 by simp [logisticCorrelation]] at h
  rw [h]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

section ClosePair

open scoped InnerProductSpace
open Submodule
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)

local notation "E₃" => EuclideanSpace ℂ (Fin 3)
local notation "M₃" => Matrix (Fin 3) (Fin 3) ℂ

private theorem exists_unit_orthogonal_pair (x y : E₃) :
    ∃ u : E₃, ‖u‖ = 1 ∧ ⟪x, u⟫_ℂ = 0 ∧ ⟪y, u⟫_ℂ = 0 := by
  classical
  let pair : Finset E₃ := {x, y}
  let K : Submodule ℂ E₃ := Submodule.span ℂ (pair : Set E₃)
  have hK : Module.finrank ℂ K ≤ 2 :=
    (finrank_span_finset_le_card (R := ℂ) pair).trans
      ((Finset.card_insert_le x {y}).trans (by simp))
  have hdim := K.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hdim
  have : Nontrivial Kᗮ :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ Kᗮ)
  obtain ⟨v, hv⟩ := exists_ne (0 : Kᗮ)
  have hv' : (v : E₃) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  let u : E₃ := ((‖(v : E₃)‖⁻¹ : ℝ) : ℂ) • (v : E₃)
  have hu : u ∈ Kᗮ := Kᗮ.smul_mem _ v.property
  refine ⟨u, ?_, K.inner_right_of_mem_orthogonal (subset_span (by simp [pair])) hu,
    K.inner_right_of_mem_orthogonal (subset_span (by simp [pair])) hu⟩
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv')

private def outer (x y : E₃) : M₃ := vecMulVec x.ofLp (star y.ofLp)

private theorem trace_outer (x y : E₃) : (outer x y).trace = ⟪y, x⟫_ℂ :=
  Matrix.trace_vecMulVec _ _

private theorem trace_outer_mul (x y z w : E₃) :
    (outer x y * outer z w).trace = ⟪y, z⟫_ℂ * ⟪w, x⟫_ℂ := by
  simp only [outer, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
    EuclideanSpace.inner_eq_star_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (star y.ofLp)]

private theorem adjoint_outer (x y : E₃) : (outer x y)ᴴ = outer y x := by
  simp [outer, Matrix.conjTranspose_vecMulVec]

private theorem norm_trace_mul_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ ‖A‖ * ‖B‖ := by
  let flatten (X : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
    WithLp.toLp 2 fun uv => X uv.1 uv.2
  have hnorm (X : Matrix n n ℂ) : ‖flatten X‖ = ‖X‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.norm_sq_eq, frobenius_sq, Fintype.sum_prod_type]
  have hinner : ⟪flatten A, flatten B⟫_ℂ = (Aᴴ * B).trace := by
    simp only [PiLp.inner_apply, flatten, RCLike.inner_apply',
      Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def]
    exact Finset.sum_comm
  simpa only [hinner, hnorm] using norm_inner_le_norm (𝕜 := ℂ) (flatten A) (flatten B)

/-- Project the identity away from a Hermitian matrix annihilating the three
rank-one projectors. The construction uses only a single correlated pair. -/
private theorem close_pair_trace_representer (z : Fin 3 → E₃)
    (hz : ∀ i, ⟪z i, z i⟫_ℂ = 1) (j : Fin 3) (hj : j ≠ 0)
    (hclose : (1 / 5 : ℝ) ≤ ‖⟪z 0, z j⟫_ℂ‖ ^ 2) :
    ∃ R : M₃, Rᴴ = R ∧ ‖R‖ ^ 2 ≤ 8 / 3 ∧
      ∀ i, (R * outer (z i) (z i)).trace = 1 := by
  obtain ⟨u, hu, hu₁, hu₂⟩ := exists_unit_orthogonal_pair (z 1) (z 2)
  let v := u - ⟪z 0, u⟫_ℂ • z 0
  let t := ‖v‖ ^ 2
  have huv₀ : ⟪z 0, v⟫_ℂ = 0 := by
    dsimp only [v]
    rw [inner_sub_right, inner_smul_right, hz, mul_one, sub_self]
  have hvv₀ : ⟪v, z 0⟫_ℂ = 0 := inner_eq_zero_symm.mp huv₀
  have huv : ⟪u, v⟫_ℂ = (t : ℂ) := by
    calc
      _ = ⟪v + ⟪z 0, u⟫_ℂ • z 0, v⟫_ℂ := by rw [show v + _ = u from sub_add_cancel _ _]
      _ = _ := by simp [huv₀, t, inner_self_eq_norm_sq_to_K]
  have hvu : ⟪v, u⟫_ℂ = (t : ℂ) := by
    rw [← inner_conj_symm, huv]
    simp
  have hvv : ⟪v, v⟫_ℂ = (t : ℂ) := by
    simp [t, inner_self_eq_norm_sq_to_K]
  have huu : ⟪u, u⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one hu
  have ht : (1 / 5 : ℝ) ≤ t := by
    let x := z 0 - ⟪u, z 0⟫_ℂ • u
    have hx : ⟪x, x⟫_ℂ = (t : ℂ) := by
      rw [← hvv]
      simp only [x, v, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hz, huu]
      rw [inner_conj_symm u (z 0)]
      ring
    have hxn : ‖x‖ ^ 2 = t := by
      have h : RCLike.re ⟪x, x⟫_ℂ = t := congrArg Complex.re hx
      rwa [inner_self_eq_norm_sq] at h
    have huzj : ⟪z j, u⟫_ℂ = 0 := by
      fin_cases j
      · exact (hj rfl).elim
      · exact hu₁
      · exact hu₂
    have hpair : ⟪x, z j⟫_ℂ = ⟪z 0, z j⟫_ℂ := by
      simp [x, inner_eq_zero_symm.mp huzj]
    have hzn : ‖z j‖ = 1 := by
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
      have h : RCLike.re ⟪z j, z j⟫_ℂ = 1 := congrArg Complex.re (hz j)
      rw [one_pow]
      rwa [inner_self_eq_norm_sq] at h
    have hc := norm_inner_le_norm (𝕜 := ℂ) x (z j)
    rw [hpair, hzn, mul_one] at hc
    exact hclose.trans ((pow_le_pow_left₀ (norm_nonneg _) hc 2).trans_eq hxn)
  let W : M₃ := (1 / 2 : ℂ) • (outer u v + outer v u)
  have hW : Wᴴ = W := by
    simp only [W, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, adjoint_outer,
      star_div₀, star_one, star_ofNat]
    rw [add_comm]
  have hTr : W.trace = (t : ℂ) := by
    simp only [W, Matrix.trace_smul, Matrix.trace_add, trace_outer, huv, hvu, smul_eq_mul]
    ring
  have hTrSq : (W * W).trace = (((t + t ^ 2) / 2 : ℝ) : ℂ) := by
    simp only [W, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.trace_smul,
      Matrix.trace_add, trace_outer_mul, hvu, huv, hvv, huu, smul_eq_mul]
    push_cast
    ring
  have hWP (i : Fin 3) : (W * outer (z i) (z i)).trace = 0 := by
    simp only [W, Matrix.smul_mul, add_mul, Matrix.trace_smul, Matrix.trace_add,
      trace_outer_mul, smul_eq_mul]
    fin_cases i
    · simp [huv₀, hvv₀]
    · simp [hu₁, inner_eq_zero_symm.mp hu₁]
    · simp [hu₂, inner_eq_zero_symm.mp hu₂]
  let c := 2 / (1 + t)
  let R : M₃ := 1 - (c : ℂ) • W
  have hR : Rᴴ = R := by simp [R, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hW]
  refine ⟨R, hR, ?_, fun i => ?_⟩
  · have hnorm : ‖R‖ ^ 2 = 3 - 2 * c * t + c ^ 2 * ((t + t ^ 2) / 2) := by
      have h : ((‖R‖ ^ 2 : ℝ) : ℂ) =
          ((3 - 2 * c * t + c ^ 2 * ((t + t ^ 2) / 2) : ℝ) : ℂ) := by
        rw [frobenius_norm_sq_eq_trace, hR]
        simp only [R, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul,
          hTr, hTrSq, smul_eq_mul, Fintype.card_fin, Nat.cast_ofNat]
        push_cast
        ring
      exact_mod_cast h
    have hden : 0 < 1 + t := by linarith
    have hratio : (1 / 3 : ℝ) ≤ 2 * t / (1 + t) :=
      (le_div_iff₀ hden).mpr (by linarith)
    rw [hnorm, show 3 - 2 * c * t + c ^ 2 * ((t + t ^ 2) / 2) = 3 - 2 * t / (1 + t) by
      dsimp [c]
      field_simp
      ring]
    linarith
  · simp only [R, sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, trace_outer, hz, hWP, smul_zero, sub_zero]

private theorem close_pair_weighted_evaluation (ω : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (j : Fin 3) (hj : j ≠ 0) (hclose : (1 / 5 : ℝ) ≤ ‖correlation ω 0 j‖ ^ 2) :
    Integrable (fun t : ℝ => petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) ∧
    ‖exponentialSum ω a 0‖ ^ 2 ≤ (8 / 3) *
      (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) := by
  obtain ⟨hInt, henergy⟩ := weighted_energy_eq_gram ω a
  obtain ⟨hPSD, hdiag, _⟩ := PetzLogisticEvaluation.exact_gram_factorization ω
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hPSD.nonneg
  let z (i : Fin 3) : E₃ := WithLp.toLp 2 fun k => B k i
  let P (i : Fin 3) := outer (z i) (z i)
  let S : M₃ := ∑ i, a i • P i
  have hdot (i j : Fin 3) : ⟪z i, z j⟫_ℂ = correlation ω i j := by
    rw [hB]
    exact (dotProduct_comm _ _)
  obtain ⟨R, hR, hRnorm, hRP⟩ := close_pair_trace_representer z
    (fun i => (hdot i i).trans (hdiag i)) j hj (by rwa [hdot])
  have hP (i : Fin 3) : (P i)ᴴ = P i := adjoint_outer _ _
  have hPair (i j : Fin 3) : (P i * P j).trace = (‖correlation ω i j‖ ^ 2 : ℂ) := by
    rw [show P i = outer (z i) (z i) from rfl, show P j = outer (z j) (z j) from rfl,
      trace_outer_mul, ← inner_conj_symm (z j) (z i), hdot]
    exact Complex.mul_conj' _
  have htrace : (Rᴴ * S).trace = ∑ i, a i := by
    simp only [hR, S, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      P, hRP, smul_eq_mul, mul_one]
  have hnorm : ‖S‖ ^ 2 = ∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2 := by
    have h := congrArg Complex.re (frobenius_norm_sq_eq_trace S)
    rw [Complex.ofReal_re] at h
    rw [h, ← Complex.ofReal_re (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2),
      henergy]
    congr 1
    simp only [S, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hP,
      Finset.sum_mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, hPair, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hEval := pow_le_pow_left₀ (norm_nonneg _) (norm_trace_mul_le R S) 2
  rw [htrace, mul_pow] at hEval
  have h := hEval.trans (mul_le_mul_of_nonneg_right hRnorm (sq_nonneg ‖S‖))
  exact ⟨hInt, by simpa [exponentialSum, hnorm] using h⟩

end ClosePair

private theorem endpoint_young (c : ℝ) (a b : ℂ) :
    c * ‖a + b‖ ^ 2 ≤ (1 + c) * (c * ‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hs : 0 ≤ ‖(c : ℂ) * a - b‖ ^ 2 := sq_nonneg _
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im] at hs ⊢
  linarith only [hs]

private theorem entry_centering [DecidableEq e] (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) (u v : e) :
    let x := logistic (sourceGap p j)
    let y := logistic (referenceGap q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    let A := sourceOff U X i j u v
    let B := referenceOff p q U Y i j u v
    let C := central p q U X Y i j u v
    let m := C + (x : ℂ) * A + (y : ℂ) * B
    let n := centeredEndpoint x y (sourceOff U X i j) (referenceOff p q U Y i j) u v
    let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v)
    Integrable (fun t => petzWeight t * ‖F t‖ ^ 2) ∧
    λ₀ * ‖F 0‖ ^ 2 ≤ (1 + λ₀) * (λ₀ * ‖m‖ ^ 2 + ‖n‖ ^ 2) ∧
    (∫ t, petzWeight t * ‖F t‖ ^ 2) = ‖m‖ ^ 2 +
      ((1-x^2)*‖A‖^2 + (1-y^2)*‖B‖^2 + 2*(z-x*y)*(star A*B).re) := by
  dsimp only
  let C := central p q U X Y i j u v
  let A := sourceOff U X i j u v
  let B := referenceOff p q U Y i j u v
  let α := sourceGap p j
  let β := referenceGap q i
  let x := logistic α
  let y := logistic β
  let f := exponentialSum ![0, α, β] ![C, A, B]
  have hnorm (t : ℝ) :
      ‖mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v)‖ = ‖f (t : ℂ)‖ := by
    rw [mixedBoundary_qubit_entry, norm_mul, Complex.norm_exp]
    simp [f, α, β, A, B, C, frequency, Complex.mul_re, Complex.mul_im]
  simp only [hnorm]
  refine ⟨(scalar_energy α β C A B).1, ?_, (scalar_energy α β C A B).2⟩
  have hf : f 0 = C + A + B := by
    simp [f, exponentialSum, Fin.sum_univ_three]
  rw [Complex.ofReal_zero, hf]
  have hsum : C + A + B = C + (x : ℂ) * A + (y : ℂ) * B +
      centeredEndpoint x y (sourceOff U X i j) (referenceOff p q U Y i j) u v := by
    simp only [centeredEndpoint, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change C + A + B = _ + ((1 - (x : ℂ)) * A + (1 - (y : ℂ)) * B)
    ring
  rw [hsum]
  exact endpoint_young _ _ _

private theorem block_centering [DecidableEq e] (p q : Qubit → ℝ) (U : Matrix Qubit Qubit ℂ)
    (X Y : Matrix (Qubit × e) (Qubit × e) ℂ) (i j : Qubit) :
    let x := logistic (sourceGap p j)
    let y := logistic (referenceGap q i)
    let z := logistic (sourceGap p j - referenceGap q i)
    let A := sourceOff U X i j
    let B := referenceOff p q U Y i j
    let C := central p q U X Y i j
    let M := C + (x : ℂ) • A + (y : ℂ) • B
    let G (t : ℝ) := ∑ u : e, ∑ v : e,
      ‖mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t (i,u) (j,v)‖ ^ 2
    Integrable (fun t => petzWeight t * G t) ∧
    λ₀ * G 0 ≤ (1 + λ₀) * (λ₀ * ‖M‖ ^ 2 + ‖centeredEndpoint x y A B‖ ^ 2) ∧
    (∫ t, petzWeight t * G t) = ‖M‖ ^ 2 + centeredEnergy x y z A B := by
  dsimp only
  have hb (u v : e) := entry_centering p q U X Y i j u v
  simp only [Finset.mul_sum]
  refine ⟨integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hb u v).1)),
    ?_, ?_⟩
  · simp only [frobenius_sq, Finset.mul_sum, ← Finset.sum_add_distrib,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (hb u v).2.1
  · rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hb u v).1))]
    simp_rw [integral_finsetSum _ (fun v _ => (hb _ v).1)]
    simp only [centeredEnergy, innerRe, frobenius_sq, Finset.mul_sum, ← Finset.sum_add_distrib,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => (hb u v).2.2

private theorem opposite_gaps (p q : Qubit → ℝ) (i j : Qubit) :
    sourceGap p j.rev = -sourceGap p j ∧ referenceGap q i.rev = -referenceGap q i := by
  simp only [sourceGap, referenceGap, Fin.rev_rev, neg_sub, and_self]

/-- Opposite mixed spectral blocks, in any finite environment, have the
centered logistic endpoint bound when the two marginal correlations and the
difference of those correlations satisfy the scalar inequalities displayed here. -/
private theorem mixedBoundary_opposite_blocks_evaluation [DecidableEq e]
    (p q : Fin 2 → ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Fin 2 × e) (Fin 2 × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (i j : Fin 2)
    (hx : logistic (sourceGap p j) ≤ 1 / 5) (hy : logistic (referenceGap q i) ≤ 1 / 5)
    (hgap : (logistic (sourceGap p j) - logistic (referenceGap q i)) ^ 2 ≤
      (7 / 25) * (1 - logistic (sourceGap p j - referenceGap q i))) :
    let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
    let G (t : ℝ) := ∑ u : e, ∑ v : e,
      (‖F t (i,u) (j,v)‖ ^ 2 + ‖F t (i.rev,u) (j.rev,v)‖ ^ 2)
    G 0 ≤ (2 + Real.sqrt 2 / 2) * (∫ t, petzWeight t * G t) := by
  dsimp only
  let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
  let G (i j : Fin 2) (t : ℝ) := ∑ u : e, ∑ v : e, ‖F t (i,u) (j,v)‖ ^ 2
  have hG (t : ℝ) : (∑ u : e, ∑ v : e, (‖F t (i,u) (j,v)‖ ^ 2 +
      ‖F t (i.rev,u) (j.rev,v)‖ ^ 2)) = G i j t + G i.rev j.rev t := by
    simp only [G, Finset.sum_add_distrib]
  change (∑ u : e, ∑ v : e, (‖F 0 (i,u) (j,v)‖ ^ 2 + ‖F 0 (i.rev,u) (j.rev,v)‖ ^ 2)) ≤
    (2 + Real.sqrt 2 / 2) * ∫ t, petzWeight t *
      (∑ u : e, ∑ v : e, (‖F t (i,u) (j,v)‖ ^ 2 + ‖F t (i.rev,u) (j.rev,v)‖ ^ 2))
  simp only [hG, mul_add]
  obtain ⟨hi, hEval, hInt⟩ := block_centering p q U X Y i j
  obtain ⟨hi', hEval', hInt'⟩ := block_centering p q U X Y i.rev j.rev
  dsimp only at hi hEval hInt hi' hEval' hInt'
  obtain ⟨hα, hβ⟩ := opposite_gaps p q i j
  rw [hα, hβ, logistic_neg, logistic_neg, show -sourceGap p j - -referenceGap q i =
    -(sourceGap p j - referenceGap q i) by ring, logistic_neg] at hInt'
  rw [hα, hβ, logistic_neg, logistic_neg] at hEval'
  rw [integral_add hi hi', hInt, hInt']
  have hp := physical_centered_pair p q U hU hU' X Y hX hY i j hx hy hgap
  dsimp only at hp
  have hpos : 0 < λ₀ := by linarith only [root_bounds.1]
  apply (mul_le_mul_iff_right₀ hpos).mp
  change λ₀ * (G i j 0 + G i.rev j.rev 0) ≤ _
  have hc : 0 ≤ 1 + λ₀ := by linarith
  nlinarith only [hEval, hEval', mul_le_mul_of_nonneg_left hp hc]

end Blocks


local notation "K₂" => (2 + Real.sqrt 2 / 2)

private theorem qubit_evaluation {e : Type*} [Fintype e] [DecidableEq e]
    (p q : Fin 2 → ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Fin 2 × e) (Fin 2 × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hx : ∀ j, logistic (sourceGap p j) ≤ 1 / 5)
    (hy : ∀ i, logistic (referenceGap q i) ≤ 1 / 5)
    (hgap : ∀ i j, (logistic (sourceGap p j) - logistic (referenceGap q i)) ^ 2 ≤
      (7 / 25) * (1 - logistic (sourceGap p j - referenceGap q i))) :
    let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
    ‖F 0‖ ^ 2 ≤ K₂ * (∫ t, petzWeight t * ‖F t‖ ^ 2) := by
  dsimp only
  let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
  let G (i j : Fin 2) (t : ℝ) := ∑ u : e, ∑ v : e, ‖F t (i,u) (j,v)‖ ^ 2
  have hG (i j : Fin 2) (t : ℝ) : (∑ u : e, ∑ v : e,
      (‖F t (i,u) (j,v)‖ ^ 2 + ‖F t (i.rev,u) (j.rev,v)‖ ^ 2)) = G i j t + G i.rev j.rev t := by
    simp only [G, Finset.sum_add_distrib]
  have hnorm (t : ℝ) : ‖F t‖ ^ 2 = (G 0 0 t + G 1 1 t) + (G 0 1 t + G 1 0 t) := by
    rw [frobenius_sq, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib, G]
    ring
  have hEval (i j : Fin 2) := mixedBoundary_opposite_blocks_evaluation p q U hU hU' X Y hX hY
    i j (hx j) (hy i) (hgap i j)
  dsimp only at hEval
  have he (i j : Fin 2) : G i j 0 + G i.rev j.rev 0 ≤
      K₂ * (∫ t, petzWeight t * G i j t + petzWeight t * G i.rev j.rev t) := by
    have h := hEval i j
    change (∑ u : e, ∑ v : e,
      (‖F 0 (i,u) (j,v)‖ ^ 2 + ‖F 0 (i.rev,u) (j.rev,v)‖ ^ 2)) ≤
      _ * (∫ t, petzWeight t * (∑ u : e, ∑ v : e,
        (‖F t (i,u) (j,v)‖ ^ 2 + ‖F t (i.rev,u) (j.rev,v)‖ ^ 2))) at h
    simpa only [hG, mul_add] using h
  have hInt (i j : Fin 2) : Integrable (fun t => petzWeight t * G i j t) :=
    (block_centering p q U X Y i j).1
  change ‖F 0‖ ^ 2 ≤ K₂ * (∫ t, petzWeight t * ‖F t‖ ^ 2)
  simp only [hnorm, mul_add]
  have ht := integral_add ((hInt 0 0).add (hInt 1 1)) ((hInt 0 1).add (hInt 1 0))
  change (∫ t, (petzWeight t * G 0 0 t + petzWeight t * G 1 1 t) +
      (petzWeight t * G 0 1 t + petzWeight t * G 1 0 t)) =
    (∫ t, petzWeight t * G 0 0 t + petzWeight t * G 1 1 t) +
    (∫ t, petzWeight t * G 0 1 t + petzWeight t * G 1 0 t) at ht
  rw [ht]
  have h₀ := he 0 0
  have h₁ := he 0 1
  change G 0 0 0 + G 1 1 0 ≤ K₂ *
    (∫ t, petzWeight t * G 0 0 t + petzWeight t * G 1 1 t) at h₀
  change G 0 1 0 + G 1 0 0 ≤ K₂ *
    (∫ t, petzWeight t * G 0 1 t + petzWeight t * G 1 0 t) at h₁
  rw [mul_add]
  exact add_le_add h₀ h₁


section Reindex

variable {k l e : Type*} [Fintype k] [Fintype l] [Fintype e]
  [DecidableEq k] [DecidableEq l] [DecidableEq e]

private theorem diagonalPhase_reindex {s s' : Type*} [DecidableEq s] [DecidableEq s']
    (f : s' ≃ s) (p : s → ℝ) (z : ℂ) :
    (diagonalPhase p z).submatrix f f = diagonalPhase (p ∘ f) z := by
  rw [diagonalPhase, diagonalPhase, Matrix.submatrix_diagonal_equiv]
  rfl

private theorem mixed_reindex (f : Fin 2 ≃ k) (g : Fin 2 ≃ l)
    (p : k → ℝ) (q : l → ℝ) (X : Matrix (k × e) (k × e) ℂ)
    (Y : Matrix (l × e) (l × e) ℂ) (C : Matrix (l × e) (k × e) ℂ) (t : ℝ) :
    let f' := f.prodCongr (Equiv.refl e)
    let g' := g.prodCongr (Equiv.refl e)
    (mixedBoundary p q X Y C t).submatrix g' f' =
      mixedBoundary (p ∘ f) (q ∘ g) (X.submatrix f' f') (Y.submatrix g' g')
        (C.submatrix g' f') t := by
  dsimp only
  let f' := f.prodCongr (Equiv.refl e)
  let g' := g.prodCongr (Equiv.refl e)
  change (mixedBoundary p q X Y C t).submatrix g' f' = _
  let z := (t : ℂ) * Complex.I
  let h := ((1 / 2 : ℝ) : ℂ)
  let P (w : ℂ) := diagonalPhase (p ∘ Prod.fst : k × e → ℝ) w
  let Q (w : ℂ) := diagonalPhase (q ∘ Prod.fst : l × e → ℝ) w
  change (Q (-z) * C * P z * X - Y * Q (-h - z) * C * P (h + z)).submatrix g' f' = _
  change (Q (-z) * C * P z * X).submatrix g' f' -
    (Y * Q (-h - z) * C * P (h + z)).submatrix g' f' = _
  rw [← Matrix.submatrix_mul_equiv _ _ g' f' f', ← Matrix.submatrix_mul_equiv _ _ g' f' f',
    ← Matrix.submatrix_mul_equiv _ _ g' g' f']
  rw [← Matrix.submatrix_mul_equiv _ _ g' f' f', ← Matrix.submatrix_mul_equiv _ _ g' g' f',
    ← Matrix.submatrix_mul_equiv _ _ g' g' g']
  simp only [P, Q, diagonalPhase_reindex]
  rfl

private theorem submatrix_norm_sq {r c r' c' : Type*}
    [Fintype r] [Fintype c] [Fintype r'] [Fintype c'] (A : Matrix r c ℂ)
    (f : r' ≃ r) (g : c' ≃ c) : ‖A.submatrix f g‖ ^ 2 = ‖A‖ ^ 2 := by
  simp only [frobenius_sq, Matrix.submatrix_apply]
  calc
    _ = ∑ i : r', ∑ j : c, ‖A (f i) j‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => g.sum_comp (fun j : c => ‖A (f i) j‖ ^ 2)
    _ = _ := f.sum_comp (fun i : r => ∑ j : c, ‖A i j‖ ^ 2)

end Reindex

section Physical

universe u

variable {a b e : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b] [Fintype e] [DecidableEq e]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}
  (M : SupportedRelativeModularModel Φ ρ σ) (W : Matrix (b × e) a ℂ)

private theorem physical_evaluation (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (f : Fin 2 ≃ M.data.K) (g : Fin 2 ≃ M.data.L)
    (hx : ∀ j, logistic (sourceGap (M.data.pk ∘ f) j) ≤ 1 / 5)
    (hy : ∀ i, logistic (referenceGap (M.data.ql ∘ g) i) ≤ 1 / 5)
    (hgap : ∀ i j, (logistic (sourceGap (M.data.pk ∘ f) j) -
        logistic (referenceGap (M.data.ql ∘ g) i)) ^ 2 ≤
      (7 / 25) * (1 - logistic (sourceGap (M.data.pk ∘ f) j -
        referenceGap (M.data.ql ∘ g) i))) :
    ‖lowerAmplitude M W 0 - upperAmplitude M W 0‖ ^ 2 ≤
      K₂ * (∫ t, petzWeight t * ‖lowerAmplitude M W t - upperAmplitude M W t‖ ^ 2) := by
  let D := M.data
  let f' := f.prodCongr (Equiv.refl e)
  let g' := g.prodCongr (Equiv.refl e)
  let P₀ := columns D.hT.1
  let Q₀ := columns D.hQ.1
  let P := outputSourceColumns M (e := e)
  let Q := outputReferenceColumns M (e := e)
  let C : Matrix D.L D.K ℂ := Q₀ᴴ * P₀
  let U : Matrix (Fin 2) (Fin 2) ℂ := C.submatrix g f
  let X₀ := Pᴴ * sourceRoot M W * P
  let Y₀ := Qᴴ * referenceRoot M W * Q
  let X := X₀.submatrix f' f'
  let Y := Y₀.submatrix g' g'
  have hQP : (Q₀ * Q₀ᴴ) * (P₀ * P₀ᴴ) = P₀ * P₀ᴴ := by
    rw [columns_support D.hQ, columns_support D.hT, ← power_zero D.hT]
    exact power_of_support_left D.hT _ (petz_output_support_projection M) 0
  have hQcol : (Q₀ * Q₀ᴴ) * P₀ = P₀ := by
    have h := congrArg (fun A : Matrix b b ℂ => A * P₀) hQP
    have hP₀ : P₀ᴴ * P₀ = 1 := columns_isometry D.hT.1
    simpa only [Matrix.mul_assoc, hP₀, Matrix.mul_one] using h
  have hC : Cᴴ * C = 1 := by
    dsimp only [C]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Q₀, hQcol, columns_isometry D.hT.1]
  have hU : Uᴴ * U = 1 := by
    dsimp only [U]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ f g f, hC,
      Matrix.submatrix_one_equiv]
  have hU' : U * Uᴴ = 1 := (mul_eq_one_comm (a := Uᴴ) (b := U)).mp hU
  have hX : X.IsHermitian := by
    change (X₀.submatrix f' f')ᴴ = _
    rw [Matrix.conjTranspose_submatrix]
    congr 1
    dsimp only [X₀]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, sourceRoot_selfAdjoint,
      Matrix.mul_assoc]
  have hY : Y.IsHermitian := by
    change (Y₀.submatrix g' g')ᴴ = _
    rw [Matrix.conjTranspose_submatrix]
    congr 1
    dsimp only [Y₀]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      referenceRoot_selfAdjoint,
      Matrix.mul_assoc]
  have hTensor : (Qᴴ * P).submatrix g' f' = U ⊗ₖ (1 : Matrix e e ℂ) := by
    have h : Qᴴ * P = tensorId (e := e) C := by
      change (tensorId Q₀)ᴴ * tensorId P₀ = _
      rw [tensorId_adjoint, tensorId_mul]
    rw [h]
    rfl
  have hNorm (t : ℝ) : ‖lowerAmplitude M W t - upperAmplitude M W t‖ ^ 2 =
      ‖mixedBoundary (D.pk ∘ f) (D.ql ∘ g) X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t‖ ^ 2 := by
    have hMixed : (mixedBoundary D.pk D.ql X₀ Y₀ (Qᴴ * P) t).submatrix g' f' =
        mixedBoundary (D.pk ∘ f) (D.ql ∘ g) X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t := by
      rw [← hTensor]
      exact mixed_reindex f g D.pk D.ql X₀ Y₀ (Qᴴ * P) t
    calc
      _ = ‖mixedBoundary D.pk D.ql X₀ Y₀ (Qᴴ * P) t‖ ^ 2 :=
        physical_mixed_sq M W hW hAction t
      _ = _ := by rw [← hMixed, submatrix_norm_sq]
  simp only [hNorm]
  exact qubit_evaluation (D.pk ∘ f) (D.ql ∘ g) U hU hU' X Y hX hY hx hy hgap

omit [DecidableEq e] in
private theorem physical_trace_bound (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (f : Fin 2 ≃ M.data.K) (g : Fin 2 ≃ M.data.L)
    (hx : ∀ j, logistic (sourceGap (M.data.pk ∘ f) j) ≤ 1 / 5)
    (hy : ∀ i, logistic (referenceGap (M.data.ql ∘ g) i) ≤ 1 / 5)
    (hgap : ∀ i j, (logistic (sourceGap (M.data.pk ∘ f) j) -
        logistic (referenceGap (M.data.ql ∘ g) i)) ^ 2 ≤
      (7 / 25) * (1 - logistic (sourceGap (M.data.pk ∘ f) j -
        referenceGap (M.data.ql ∘ g) i))) :
    traceNorm (M.data.R - recoveredState M.data) ^ 2 ≤
      (8 + 2 * Real.sqrt 2) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  classical
  convert (trace_error_le_boundary M W hW hAction).trans
      (mul_le_mul_of_nonneg_left
        ((physical_evaluation M W hW hAction f g hx hy hgap).trans
          (mul_le_mul_of_nonneg_left (full_logistic_physical M W hW hAction)
            (by positivity : 0 ≤ K₂))) (by norm_num : (0 : ℝ) ≤ 4)) using 1
  ring

end Physical

section Channel

universe u

variable {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

/-- The ordinary Petz channel has squared trace error bounded by eight times the
entropy loss for rank-one source outputs when the reference output has rank at
most two. For two rank-two outputs with logistic correlations at most one fifth,
the same channel has coefficient `8 + 2√2`. -/
theorem ordinary_petz_traceNorm_sq_le_of_qubit_gaps
    (Φ : QuantumChannel a b) (σ : DensityState a) :
    let K := (actual_kraus_representation Φ).kraus
    let S := CStarMatrix.ofMatrix.symm σ.1
    let Q := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    let H := cfc Real.sqrt S
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, H * (K c)ᴴ * W * X * W * K c * H) +
            Matrix.trace ((1 - P) * X) • S) ∧
      recovery.mapState (Φ.mapState σ) = σ ∧
      ∀ (ρ : DensityState a) (support : SupportContained ρ σ),
        let M := supported_relative_modular_model Φ ρ σ support
        let error := traceNorm (CStarMatrix.ofMatrix.symm ρ.1 -
          CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1) ^ 2
        let Δ := finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
        M.data.Q.rank ≤ 2 →
          (M.data.T.rank ≤ 1 → error ≤ 8 * Δ) ∧
          (M.data.T.rank = 2 →
            (∀ j k : M.data.K, j ≠ k →
              logistic (Real.log (M.data.pk j) - Real.log (M.data.pk k)) ≤ 1 / 5) →
            (∀ i l : M.data.L, i ≠ l →
              logistic (Real.log (M.data.ql i) - Real.log (M.data.ql l)) ≤ 1 / 5) →
            error ≤ (8 + 2 * Real.sqrt 2) * Δ) := by
  classical
  dsimp only
  obtain ⟨recovery, hAction, hReference, _⟩ :=
    D5.S3.Quantum.Recovery.CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery
      Φ σ
  refine ⟨recovery, hAction, hReference, ?_⟩
  intro ρ support hQ
  let M := supported_relative_modular_model Φ ρ σ support
  let D := M.data
  have hTrace : Matrix.trace ((1 - spectralSupport D.Q) * D.T) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, petz_output_support_projection M, sub_self,
      Matrix.trace_zero]
  have hr := hAction D.T
  rw [hTrace, zero_smul, add_zero] at hr
  have hRecovered :
      CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1 = recoveredState D := by
    refine hr.trans ?_
    simp only [recoveredState, krausAdjoint, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rw [hRecovered]
  obtain ⟨V, hV, hDilate⟩ := exists_retainedFirst_stinespring Φ
  constructor
  · intro hT
    have hlevels : levelCount D.pk + levelCount D.ql - 1 ≤ 2 := by
      have hTP := (levelCount_le_card D.pk).trans_eq (card_positive_eigenvalues D.hT)
      have hQP := (levelCount_le_card D.ql).trans_eq (card_positive_eigenvalues D.hQ)
      change D.Q.rank ≤ 2 at hQ
      change D.T.rank ≤ 1 at hT
      change levelCount D.pk ≤ D.T.rank at hTP
      change levelCount D.ql ≤ D.Q.rank at hQP
      omega
    have hΔ : 0 ≤ finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) :=
      (integral_nonneg (fun t => mul_nonneg (petzWeight_pos t).le (sq_nonneg _))).trans
        (full_logistic_physical M V hV hDilate)
    refine (trace_sq_le_of_dilation M V hV hDilate).trans ?_
    apply mul_le_mul_of_nonneg_right _ hΔ
    calc
      _ ≤ 4 * ((2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hlevels) (by norm_num)
      _ = 8 := by norm_num
  · intro hT hPgap hQgap
    have hQ₂ : D.Q.rank = 2 := le_antisymm hQ
      (by simpa only [hT] using output_rank_le M)
    let f := (Fintype.equivFinOfCardEq ((card_positive_eigenvalues D.hT).trans hT)).symm
    let g := (Fintype.equivFinOfCardEq ((card_positive_eigenvalues D.hQ).trans hQ₂)).symm
    have hOpp (i : Fin 2) : i.rev ≠ i := by
      fin_cases i <;> decide
    have hs (j : Fin 2) : logistic (sourceGap (D.pk ∘ f) j) ≤ 1 / 5 :=
      hPgap _ _ (fun he => hOpp j (f.injective he))
    have hq (i : Fin 2) : logistic (referenceGap (D.ql ∘ g) i) ≤ 1 / 5 :=
      hQgap _ _ (fun he => hOpp i (g.injective he.symm))
    exact physical_trace_bound M V hV hDilate f g hs hq (fun i j => logistic_gap _ _ (hs j) (hq i))

#print axioms ordinary_petz_traceNorm_sq_le_of_qubit_gaps

end Channel


end D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
