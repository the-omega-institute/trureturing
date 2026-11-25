/- GID: D5/S3/Quantum/Recovery/PetzRetainedQubitPairing
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzRetainedQubitPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite retained-qubit blocks share the norms of their noncentral coefficients. -/

import D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates
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

open D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates (close_pair_weighted_evaluation)
open private root_bounds centered_quadratic innerRe halfRatio pairedAngle pairedAngle_bounds
  halfRatio_shape sourceOff referenceOff paired_inner_bound sourceGap referenceGap
  centeredEndpoint norm_centeredEndpoint centeredEnergy central mixedBoundary_qubit_entry from
  D5.S3.Quantum.Recovery.PetzQubitBoundaryEstimates

namespace D5.S3.Quantum.Recovery.PetzRetainedQubitPairing

local notation "d" => (Real.sqrt 2 / 2)
local notation "λ₀" => (1 + Real.sqrt 2 / 2)

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


private theorem qubit_close_evaluation {e : Type*} [Fintype e] [DecidableEq e]
    (p q : Fin 2 → ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (X Y : Matrix (Fin 2 × e) (Fin 2 × e) ℂ)
    (hclose : ∀ i j, (1 / 5 : ℝ) ≤ logistic (sourceGap p j) ∨
      (1 / 5 : ℝ) ≤ logistic (referenceGap q i)) :
    let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
    ‖F 0‖ ^ 2 ≤ (8 / 3) * (∫ t, petzWeight t * ‖F t‖ ^ 2) := by
  dsimp only
  let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
  have hentry (r c : Fin 2 × e) :
      Integrable (fun t => petzWeight t * ‖F t r c‖ ^ 2) ∧
      ‖F 0 r c‖ ^ 2 ≤ (8 / 3) * (∫ t, petzWeight t * ‖F t r c‖ ^ 2) := by
    obtain ⟨i, u⟩ := r
    obtain ⟨j, v⟩ := c
    let ω : Fin 3 → ℝ := ![0, sourceGap p j, referenceGap q i]
    let a : Fin 3 → ℂ :=
      ![central p q U X Y i j u v, sourceOff U X i j u v, referenceOff p q U Y i j u v]
    have hnorm (t : ℝ) : ‖F t (i,u) (j,v)‖ = ‖exponentialSum ω a (t : ℂ)‖ := by
      dsimp only [F]
      rw [mixedBoundary_qubit_entry, norm_mul, Complex.norm_exp]
      simp [ω, a, frequency, Complex.mul_re, Complex.mul_im]
    simp only [hnorm]
    have hcorr (k : Fin 3) : ‖correlation ω 0 k‖ ^ 2 = logistic (ω k) := by
      have h := logistic_correlation ω 0 k
      have hzero : ω 0 = 0 := rfl
      rw [hzero, sub_zero] at h
      exact_mod_cast h
    rcases hclose i j with hs | hq
    · exact close_pair_weighted_evaluation ω a 1 (by decide) (by rwa [hcorr])
    · exact close_pair_weighted_evaluation ω a 2 (by decide) (by rwa [hcorr])
  simp only [F, frobenius_sq, Finset.mul_sum]
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun c _ => (hentry r c).1))]
  simp_rw [integral_finsetSum _ (fun c _ => (hentry _ c).1), Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun c _ => (hentry r c).2

private theorem logistic_eq_at_zero (gap : Fin 2 → ℝ) (hgap : gap 1 = -gap 0)
    (i : Fin 2) : logistic (gap i) = logistic (gap 0) := by
  fin_cases i
  · rfl
  · change logistic (gap 1) = _
    rw [hgap, logistic_neg]

private theorem qubit_evaluation_all_gaps {e : Type*} [Fintype e] [DecidableEq e]
    (p q : Fin 2 → ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (X Y : Matrix (Fin 2 × e) (Fin 2 × e) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    let F (t : ℝ) := mixedBoundary p q X Y (U ⊗ₖ (1 : Matrix e e ℂ)) t
    ‖F 0‖ ^ 2 ≤ K₂ * (∫ t, petzWeight t * ‖F t‖ ^ 2) := by
  have hs := logistic_eq_at_zero (sourceGap p) (opposite_gaps p q 0 0).1
  have hq := logistic_eq_at_zero (referenceGap q) (opposite_gaps p q 0 0).2
  by_cases hfar : logistic (sourceGap p 0) ≤ 1 / 5 ∧ logistic (referenceGap q 0) ≤ 1 / 5
  · have hx (j : Fin 2) := (hs j).le.trans hfar.1
    have hy (i : Fin 2) := (hq i).le.trans hfar.2
    exact qubit_evaluation p q U hU hU' X Y hX hY hx hy
      (fun i j => logistic_gap _ _ (hx j) (hy i))
  · have hc (i j : Fin 2) : (1 / 5 : ℝ) ≤ logistic (sourceGap p j) ∨
        (1 / 5 : ℝ) ≤ logistic (referenceGap q i) := by
      rw [hs, hq]
      rcases not_and_or.mp hfar with hs' | hq'
      · exact Or.inl (le_of_lt (lt_of_not_ge hs'))
      · exact Or.inr (le_of_lt (lt_of_not_ge hq'))
    exact (qubit_close_evaluation p q U X Y hc).trans
      (mul_le_mul_of_nonneg_right (by linarith only [root_bounds.1])
        (integral_nonneg fun t => mul_nonneg (petzWeight_pos t).le (sq_nonneg _)))


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

private theorem physical_evaluation_of_blocks (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (f : Fin 2 ≃ M.data.K) (g : Fin 2 ≃ M.data.L)
    (hEval : ∀ (U : Matrix (Fin 2) (Fin 2) ℂ), Uᴴ * U = 1 → U * Uᴴ = 1 →
      ∀ (X Y : Matrix (Fin 2 × e) (Fin 2 × e) ℂ), X.IsHermitian → Y.IsHermitian →
      let F (t : ℝ) := mixedBoundary (M.data.pk ∘ f) (M.data.ql ∘ g) X Y
        (U ⊗ₖ (1 : Matrix e e ℂ)) t
      ‖F 0‖ ^ 2 ≤ K₂ * (∫ t, petzWeight t * ‖F t‖ ^ 2)) :
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
  exact hEval U hU hU' X Y hX hY

private theorem physical_trace_bound_of_evaluation (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (hEval : ‖lowerAmplitude M W 0 - upperAmplitude M W 0‖ ^ 2 ≤
      K₂ * (∫ t, petzWeight t * ‖lowerAmplitude M W t - upperAmplitude M W t‖ ^ 2)) :
    traceNorm (M.data.R - recoveredState M.data) ^ 2 ≤
      (8 + 2 * Real.sqrt 2) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  classical
  convert (trace_error_le_boundary M W hW hAction).trans
      (mul_le_mul_of_nonneg_left
        (hEval.trans (mul_le_mul_of_nonneg_left (full_logistic_physical M W hW hAction)
          (by positivity : 0 ≤ K₂))) (by norm_num : (0 : ℝ) ≤ 4)) using 1
  ring

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
  exact physical_trace_bound_of_evaluation M W hW hAction
    (physical_evaluation_of_blocks M W hW hAction f g fun U hU hU' X Y hX hY =>
      qubit_evaluation _ _ U hU hU' X Y hX hY hx hy hgap)

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

/-- For every finite channel whose reference output has support rank at most two,
the ordinary Petz channel has squared full trace-norm error bounded by
`(8 + 2√2) * Δ` for every supported input, where `Δ` is the Umegaki entropy loss. -/
theorem ordinary_petz_traceNorm_sq_le_of_qubit_output
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
        M.data.Q.rank ≤ 2 → error ≤ (8 + 2 * Real.sqrt 2) * Δ := by
  classical
  dsimp only
  obtain ⟨recovery, hAction, hReference, hGaps⟩ :=
    ordinary_petz_traceNorm_sq_le_of_qubit_gaps Φ σ
  refine ⟨recovery, hAction, hReference, ?_⟩
  intro ρ support hQ
  let M := supported_relative_modular_model Φ ρ σ support
  let D := M.data
  obtain ⟨V, hV, hDilate⟩ := exists_retainedFirst_stinespring Φ
  by_cases hT : D.T.rank ≤ 1
  · have hΔ : 0 ≤ finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) :=
      (integral_nonneg (fun t => mul_nonneg (petzWeight_pos t).le (sq_nonneg _))).trans
        (full_logistic_physical M V hV hDilate)
    exact ((hGaps ρ support hQ).1 hT).trans
      (mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg (2 : ℝ)]) hΔ)
  · have hT₂ : D.T.rank = 2 := by
      have hr : D.T.rank ≤ D.Q.rank := output_rank_le M
      change D.Q.rank ≤ 2 at hQ
      omega
    have hQ₂ : D.Q.rank = 2 := le_antisymm hQ
      (by simpa only [hT₂] using output_rank_le M)
    let f := (Fintype.equivFinOfCardEq ((card_positive_eigenvalues D.hT).trans hT₂)).symm
    let g := (Fintype.equivFinOfCardEq ((card_positive_eigenvalues D.hQ).trans hQ₂)).symm
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
    exact physical_trace_bound_of_evaluation M V hV hDilate
      (physical_evaluation_of_blocks M V hV hDilate f g
        (qubit_evaluation_all_gaps (D.pk ∘ f) (D.ql ∘ g)))

#print axioms ordinary_petz_traceNorm_sq_le_of_qubit_output

#print axioms ordinary_petz_traceNorm_sq_le_of_qubit_gaps

end Channel


end D5.S3.Quantum.Recovery.PetzRetainedQubitPairing
