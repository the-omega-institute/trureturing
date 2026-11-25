/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/RankFourReference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Aligned rank-four extremal eigenvectors control four complementary Fourier and coordinate amplitudes. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierGeometry

/-! The extreme rays and the four complementary tail rows of a critical rank-four mask. -/

open InnerProductSpace QuantumPhaseEstimationGeneral
open scoped BigOperators ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

local notation "law" => basisLaw coordinateBasisFive fourierBasisFive

private def rankFourTailPair : Finset Idx := {1, 4}

private def rankFourTailRows : Finset GeometryRow :=
  rankFourTailPair.disjSum rankFourTailPair

private theorem rankFourTailPair_not_mem {j : Idx} (hj : j ∈ rankFourTailPair) :
    j ∉ centeredPair := by
  simp only [rankFourTailPair, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl <;> decide

private theorem rankFourTailRows_not_mem {r : GeometryRow} (hr : r ∈ rankFourTailRows) :
    r ∉ centeredRankFour := by
  cases r <;>
    simp only [rankFourTailRows, centeredRankFour, Finset.inl_mem_disjSum,
      Finset.inr_mem_disjSum] at hr ⊢ <;>
    exact rankFourTailPair_not_mem hr

private theorem law_eq_amplitude (x : CoordinateFive) (r : GeometryRow) :
    law x r = ‖geometryAmplitude x r‖ ^ 2 := by
  rw [geometryAmplitude_eq_inner]
  cases r <;> rfl

private theorem amplitude_smul (c : ℂ) (x : CoordinateFive) (r : GeometryRow) :
    geometryAmplitude (c • x) r = c * geometryAmplitude x r := by
  simp only [geometryAmplitude_eq_inner, inner_smul_right]

private theorem amplitude_add (x y : CoordinateFive) (r : GeometryRow) :
    geometryAmplitude (x + y) r = geometryAmplitude x r + geometryAmplitude y r := by
  simp only [geometryAmplitude_eq_inner, inner_add_right]

/-- Interchanging the two bases preserves the modulus of a cross-pair coefficient. -/
private theorem rankFour_cross_norm (odd : Bool) (j : Idx) :
    ‖geometryAmplitude (centeredFourier odd) (.inl j)‖ =
      ‖geometryAmplitude (centeredStandard odd) (.inr j)‖ := by
  let s : ℂ := if odd then -1 else 1
  let p : ℂ := if odd then Complex.I else 1
  have hs : conj s = s := by cases odd <;> simp [s]
  have hp : ‖p‖ = 1 := by cases odd <;> simp [p, Complex.norm_I]
  have hsym (i k : Idx) : ⟪coordinateBasisFive i, fourierBasisFive k⟫_ℂ =
      ⟪coordinateBasisFive k, fourierBasisFive i⟫_ℂ := by
    rw [five_cross_entry, five_cross_entry, kernel_symm]
  let z := ⟪coordinateBasisFive 2, fourierBasisFive j⟫_ℂ +
    s * ⟪coordinateBasisFive 3, fourierBasisFive j⟫_ℂ
  have hl : geometryAmplitude (centeredFourier odd) (.inl j) = (p * rootHalf) * z := by
    simp only [geometryAmplitude_eq_inner, Sum.elim_inl, centeredFourier, inner_smul_right,
      inner_add_right]
    rw [hsym j 2, hsym j 3] <;> rfl
  have hr : geometryAmplitude (centeredStandard odd) (.inr j) = rootHalf * conj z := by
    simp only [geometryAmplitude_eq_inner, Sum.elim_inr, centeredStandard, inner_smul_right,
      inner_add_right]
    change rootHalf * (⟪fourierBasisFive j, coordinateBasisFive 2⟫_ℂ +
      s * ⟪fourierBasisFive j, coordinateBasisFive 3⟫_ℂ) = _
    simp only [z, map_add, map_mul, hs, inner_conj_symm]
  rw [hl, hr, norm_mul, norm_mul, norm_mul, hp, one_mul, Complex.norm_conj]

/-- Reflection exchanges the two unselected nonzero rows in each parity channel. -/
private theorem rankFour_cross_reflect (odd : Bool) :
    ‖geometryAmplitude (centeredStandard odd) (.inr 4)‖ =
      ‖geometryAmplitude (centeredStandard odd) (.inr 1)‖ := by
  have h (i k : Idx) : ⟪fourierBasisFive k, coordinateBasisFive i⟫_ℂ =
      conj (scale 5 * pentagonPhase (ZMod.finEquiv 5 i * ZMod.finEquiv 5 k)) := by
    rw [← inner_conj_symm, five_cross_entry, kernel_five_eq_pentagonPhase]
  have h₂ : ⟪fourierBasisFive 4, coordinateBasisFive 2⟫_ℂ =
      ⟪fourierBasisFive 1, coordinateBasisFive 3⟫_ℂ := by
    rw [h 2 4, h 3 1]
    exact congrArg (fun a => conj (scale 5 * pentagonPhase a)) (by decide)
  have h₃ : ⟪fourierBasisFive 4, coordinateBasisFive 3⟫_ℂ =
      ⟪fourierBasisFive 1, coordinateBasisFive 2⟫_ℂ := by
    rw [h 3 4, h 2 1]
    exact congrArg (fun a => conj (scale 5 * pentagonPhase a)) (by decide)
  cases odd <;>
    simp only [geometryAmplitude_eq_inner, Sum.elim_inr, centeredStandard, inner_smul_right,
      inner_add_right, h₂, h₃, Bool.false_eq_true, ite_true, ite_false, one_mul]
  · rw [add_comm]
  · rw [show rootHalf * (⟪fourierBasisFive 1, coordinateBasisFive 3⟫_ℂ +
        -1 * ⟪fourierBasisFive 1, coordinateBasisFive 2⟫_ℂ) =
      -(rootHalf * (⟪fourierBasisFive 1, coordinateBasisFive 2⟫_ℂ +
        -1 * ⟪fourierBasisFive 1, coordinateBasisFive 3⟫_ℂ)) by ring, norm_neg]

private def crossTailMass (odd : Bool) : ℝ :=
  (1 - centeredOverlap odd ^ 2 - (if odd then 0 else 2 / 5)) / 2

private theorem rankFour_cross_tail_mass (odd : Bool) {j : Idx}
    (hj : j ∈ rankFourTailPair) :
    ‖geometryAmplitude (centeredStandard odd) (.inr j)‖ ^ 2 = crossTailMass odd := by
  have hsel (k : Idx) (hk : k ∈ centeredPair) :
      ‖geometryAmplitude (centeredStandard odd) (.inr k)‖ ^ 2 =
        centeredOverlap odd ^ 2 / 2 := by
    rw [← centeredQ_amplitude hk (centeredStandard odd), Q_standard]
    rw [amplitude_smul, norm_mul, mul_pow, centered_pair_norm_fourier odd hk,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hzero : ‖geometryAmplitude (centeredStandard odd) (.inr 0)‖ ^ 2 =
      if odd then 0 else 2 / 5 := by
    rw [(centeredStandard_zero odd).2]
    cases odd
    · exact norm_center_coefficient
    · simp
  have hparseval : ∑ k : Idx, ‖geometryAmplitude (centeredStandard odd) (.inr k)‖ ^ 2 = 1 := by
    simp only [geometryAmplitude_eq_inner, Sum.elim_inr,
      fourierBasisFive.sum_sq_norm_inner_right, centeredStandard_orthonormal.norm_eq_one, one_pow]
  rw [Fin.sum_univ_five, hzero, hsel 2 (by decide), hsel 3 (by decide),
    rankFour_cross_reflect] at hparseval
  simp only [rankFourTailPair, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · unfold crossTailMass
    linarith only [hparseval]
  · rw [rankFour_cross_reflect]
    unfold crossTailMass
    linarith only [hparseval]

private theorem rankFour_ray_norm_tail (odd plus : Bool) {r : GeometryRow}
    (hr : r ∈ rankFourTailRows) :
    ‖geometryAmplitude (centeredRay false odd plus) r‖ ^ 2 =
      crossTailMass odd / (2 * (1 + principalSign plus * centeredOverlap odd)) := by
  have hL : ‖((principalLength false odd plus : ℂ)⁻¹)‖ ^ 2 =
      (2 * (1 + principalSign plus * centeredOverlap odd))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, principalLength_sq_real]
    <;> rfl
  have hs : ‖(principalSign plus : ℂ)‖ = 1 := by
    cases plus <;> simp [principalSign]
  cases r with
  | inl j =>
    have hj : j ∈ rankFourTailPair := by
      simpa only [rankFourTailRows, Finset.inl_mem_disjSum] using hr
    have hne := rankFourTailPair_not_mem hj
    have h₂ : j ≠ 2 := fun he => hne (by simp [centeredPair, he])
    have h₃ : j ≠ 3 := fun he => hne (by simp [centeredPair, he])
    have hz : geometryAmplitude (centeredStandard odd) (.inl j) = 0 := by
      simp only [geometryAmplitude_eq_inner, Sum.elim_inl, centeredStandard, inner_smul_right,
        inner_add_right, coordinateBasisFive.orthonormal.inner_eq_zero h₂,
        coordinateBasisFive.orthonormal.inner_eq_zero h₃, mul_zero, add_zero]
    simp only [centeredRay, principalStandard, Bool.false_eq_true, ite_false, amplitude_smul,
      amplitude_add, hz, zero_add,
      norm_mul, hs, one_mul, mul_pow, hL, rankFour_cross_norm odd j,
      rankFour_cross_tail_mass odd hj]
    ring
  | inr j =>
    have hj : j ∈ rankFourTailPair := by
      simpa only [rankFourTailRows, Finset.inr_mem_disjSum] using hr
    have hne := rankFourTailPair_not_mem hj
    have h₂ : j ≠ 2 := fun he => hne (by simp [centeredPair, he])
    have h₃ : j ≠ 3 := fun he => hne (by simp [centeredPair, he])
    have hz : geometryAmplitude (centeredFourier odd) (.inr j) = 0 := by
      simp only [geometryAmplitude_eq_inner, Sum.elim_inr, centeredFourier, inner_smul_right,
        inner_add_right, fourierBasisFive.orthonormal.inner_eq_zero h₂,
        fourierBasisFive.orthonormal.inner_eq_zero h₃, mul_zero, add_zero]
    simp only [centeredRay, principalStandard, Bool.false_eq_true, ite_false, amplitude_smul,
      amplitude_add, hz, mul_zero, add_zero,
      norm_mul, mul_pow, hL, rankFour_cross_tail_mass odd hj]
    ring

private theorem rankFour_top_tail_mass {r : GeometryRow} (hr : r ∈ rankFourTailRows) :
    law (centeredEigenbasis false (some (true, true))) r = (1 - sharpSigma) / 4 := by
  rw [law_eq_amplitude, centeredEigenbasis_some, rankFour_ray_norm_tail true true hr]
  simp only [crossTailMass, centeredOverlap, principalSign, ite_true, sub_zero, one_mul]
  have h : 1 + sharpSigma ≠ 0 := by linarith only [sharp_sigma_bounds.1]
  field_simp [h] <;> ring

private theorem rankFour_kernel_tail_mass {r : GeometryRow} (hr : r ∈ rankFourTailRows) :
    law (centeredEigenbasis false none) r = 2 / (7 + Real.sqrt 5) := by
  have hpair (odd : Bool) :
      (∑ plus : Bool, ‖geometryAmplitude (centeredRay false odd plus) r‖ ^ 2) =
        crossTailMass odd / (1 - centeredOverlap odd ^ 2) := by
    have hl : 0 < centeredOverlap odd := by
      cases odd <;> simp [centeredOverlap] <;> linarith [sharp_b_bounds.1, sharp_sigma_bounds.1]
    have hu : centeredOverlap odd < 1 := by
      cases odd <;> simp [centeredOverlap] <;> linarith [sharp_b_bounds.2, sharp_sigma_bounds.2]
    have h₁ : 1 - centeredOverlap odd ≠ 0 := by linarith
    have h₂ : 1 + centeredOverlap odd ≠ 0 := by linarith
    have h₃ : 1 - centeredOverlap odd ^ 2 ≠ 0 := by
      rw [show 1 - centeredOverlap odd ^ 2 =
        (1 - centeredOverlap odd) * (1 + centeredOverlap odd) by ring]
      exact mul_ne_zero h₁ h₂
    simp only [Fintype.sum_bool, rankFour_ray_norm_tail odd _ hr, principalSign,
      ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul, ← sub_eq_add_neg]
    field_simp [h₁, h₂, h₃] <;> ring
  have hodd : crossTailMass true / (1 - centeredOverlap true ^ 2) = 1 / 2 := by
    simp only [crossTailMass, centeredOverlap, ite_true, sub_zero]
    have h : 1 - sharpSigma ^ 2 ≠ 0 := by
      have hl := sharp_sigma_bounds.1
      have hu := sharp_sigma_bounds.2
      have hlt : sharpSigma ^ 2 < 1 ^ 2 :=
        (sq_lt_sq₀ (by linarith) zero_le_one).mpr (by linarith)
      linarith
    field_simp [h] <;> ring
  have heven : crossTailMass false / (1 - centeredOverlap false ^ 2) =
      1 / 2 - 2 / (7 + Real.sqrt 5) := by
    simp only [crossTailMass, centeredOverlap, Bool.false_eq_true, ite_false]
    rw [sharpB_sq, sharpD_eq, sub_sub_cancel, sharpC_sq]
    have h : 7 + Real.sqrt (5 : ℝ) ≠ 0 := by positivity
    field_simp [h] <;> ring
  have hsum := centered_row_mass_sum false r
  simp only [Fintype.sum_option, Fintype.sum_prod_type, centeredEigenbasis_some, hpair] at hsum
  simp only [Fintype.sum_bool, hodd, heven] at hsum
  rw [law_eq_amplitude]
  linarith only [hsum]

/-- Phase alignment with a unit ray, including a vanishing reference coefficient. -/
private theorem rankFour_align (x v : CoordinateFive) (hx : ‖x‖ = 1)
    (hv : ‖v‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖x - c • v‖ ^ 2 ≤ 2 * (1 - ‖⟪v, x⟫_ℂ‖ ^ 2) := by
  let z := ⟪v, x⟫_ℂ
  have hz₁ : ‖z‖ ≤ 1 := by
    simpa only [hx, hv, mul_one] using norm_inner_le_norm (𝕜 := ℂ) v x
  have hz₂ : ‖z‖ ^ 2 ≤ ‖z‖ := by
    nlinarith only [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz₁)]
  have hc : ∃ c : ℂ, ‖c‖ = 1 ∧ z * conj c = (‖z‖ : ℂ) := by
    by_cases hz : z = 0
    · exact ⟨1, norm_one, by simp [hz]⟩
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have hn' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn
      refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
          div_self hn]
      · rw [map_div₀, Complex.conj_ofReal, ← mul_div_assoc, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two, mul_div_cancel_right₀ _ hn']
  obtain ⟨c, hc, hcz⟩ := hc
  have hinner : ⟪c • v, x⟫_ℂ = (‖z‖ : ℂ) := by
    rw [inner_smul_left, mul_comm]
    exact hcz
  refine ⟨c, hc, ?_⟩
  rw [norm_sub_rev x (c • v), norm_sub_sq (𝕜 := ℂ), norm_smul, hc, hv, hx, hinner]
  change (1 * 1 : ℝ) ^ 2 - 2 * ‖z‖ + 1 ^ 2 ≤ _
  linarith only [hz₂]

private abbrev rankFourBasis := centeredEigenbasis false
private abbrev rankFourEigenvalue := centeredEigenvalue false
private def rankFourTop : CenteredEigenIndex := some (true, true)

private theorem rankFour_spectral_gap (x : CoordinateFive) (hx : ‖x‖ = 1)
    (k : CenteredEigenIndex) (w : CenteredEigenIndex → ℝ) (g : ℝ)
    (hg : 0 ≤ g) (hk : w k = 0) (hgap : ∀ i, i ≠ k → g ≤ w i) :
    0 ≤ (∑ i, w i * ‖⟪rankFourBasis i, x⟫_ℂ‖ ^ 2) ∧
      ∃ c : ℂ, ‖c‖ = 1 ∧
        g * ‖x - c • rankFourBasis k‖ ^ 2 ≤
          2 * (∑ i, w i * ‖⟪rankFourBasis i, x⟫_ℂ‖ ^ 2) := by
  classical
  let a (i : CenteredEigenIndex) := ‖⟪rankFourBasis i, x⟫_ℂ‖ ^ 2
  have hsum : ∑ i, a i = 1 := by
    simp only [a, rankFourBasis.sum_sq_norm_inner_right, hx, one_pow]
  have hrest : ∑ i ∈ Finset.univ.erase k, a i = 1 - a k := by
    have h := Finset.sum_erase_add Finset.univ a (Finset.mem_univ k)
    linarith only [h, hsum]
  have hweighted :
      ∑ i ∈ Finset.univ.erase k, w i * a i = ∑ i, w i * a i := by
    have h := Finset.sum_erase_add Finset.univ (fun i => w i * a i) (Finset.mem_univ k)
    simpa only [hk, zero_mul, add_zero] using h
  have hb : g * (1 - a k) ≤ ∑ i, w i * a i := by
    rw [← hrest, Finset.mul_sum, ← hweighted]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hgap i (Finset.mem_erase.mp hi).1) (sq_nonneg _)
  have hnonneg (i : CenteredEigenIndex) : 0 ≤ w i := by
    by_cases hi : i = k
    · rw [hi, hk]
    · exact hg.trans (hgap i hi)
  obtain ⟨c, hc, halign⟩ := rankFour_align x _ hx (rankFourBasis.norm_eq_one k)
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hnonneg i) (sq_nonneg _)), c, hc, ?_⟩
  have h := mul_le_mul_of_nonneg_left halign hg
  change g * ‖x - c • rankFourBasis k‖ ^ 2 ≤ _ at h
  linarith only [h, hb]

private theorem rankFour_top_gap (x : CoordinateFive) (hx : ‖x‖ = 1) :
    0 ≤ 1 + sharpSigma - maskMass (law x) centeredRankFour ∧
      ∃ c : ℂ, ‖c‖ = 1 ∧
        (sharpSigma - sharpB) * ‖x - c • rankFourBasis rankFourTop‖ ^ 2 ≤
          2 * (1 + sharpSigma - maskMass (law x) centeredRankFour) := by
  let w (i : CenteredEigenIndex) := 1 + sharpSigma - rankFourEigenvalue i
  have hsum :
      ∑ i, w i * ‖⟪rankFourBasis i, x⟫_ℂ‖ ^ 2 =
        1 + sharpSigma - maskMass (law x) centeredRankFour := by
    simp only [w, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
      rankFourBasis.sum_sq_norm_inner_right, hx, one_pow, mul_one]
    rw [show centeredRankFour = centeredMask false by rfl, centeredMask_mass_spectral]
  rw [← hsum]
  refine rankFour_spectral_gap x hx rankFourTop w (sharpSigma - sharpB)
    (by linarith only [sharp_sigma_bounds.1, sharp_b_bounds.2]) (by simp [rankFourTop, w,
      centeredEigenvalue, principalSign, principalOverlap, centeredOverlap]) ?_
  intro i hi
  rcases i with _ | ⟨odd, plus⟩
  · simp [w, centeredEigenvalue]
    linarith only [sharp_b_bounds.1]
  · cases odd <;> cases plus <;>
      simp [rankFourTop, w, centeredEigenvalue, principalSign, principalOverlap, centeredOverlap] at hi ⊢ <;>
      linarith only [sharp_b_bounds.1, sharp_sigma_bounds.1]

private theorem rankFour_kernel_gap (y : CoordinateFive) (hy : ‖y‖ = 1) :
    0 ≤ maskMass (law y) centeredRankFour ∧
      ∃ c : ℂ, ‖c‖ = 1 ∧
        (1 - sharpSigma) * ‖y - c • rankFourBasis none‖ ^ 2 ≤
          2 * maskMass (law y) centeredRankFour := by
  rw [show centeredRankFour = centeredMask false by rfl, centeredMask_mass_spectral]
  refine rankFour_spectral_gap y hy none rankFourEigenvalue (1 - sharpSigma)
    (by linarith only [sharp_sigma_bounds.2]) rfl ?_
  intro i hi
  rcases i with _ | ⟨odd, plus⟩
  · exact (hi rfl).elim
  · cases odd <;> cases plus <;>
      simp [centeredEigenvalue, principalSign, principalOverlap, centeredOverlap] <;>
      linarith only [sharp_b_bounds.1, sharp_b_bounds.2, sharp_sigma_bounds.1]

private theorem sqrt_law (x : CoordinateFive) (r : GeometryRow) :
    Real.sqrt (law x r) = ‖geometryAmplitude x r‖ := by
  rw [law_eq_amplitude, Real.sqrt_sq (norm_nonneg _)]

private theorem norm_amplitude_le (x : CoordinateFive) (r : GeometryRow) :
    ‖geometryAmplitude x r‖ ≤ ‖x‖ := by
  cases r with
  | inl j =>
    simpa only [geometryAmplitude_eq_inner, Sum.elim_inl, coordinateBasisFive.norm_eq_one,
      one_mul] using norm_inner_le_norm (𝕜 := ℂ) (coordinateBasisFive j) x
  | inr j =>
    simpa only [geometryAmplitude_eq_inner, Sum.elim_inr, fourierBasisFive.norm_eq_one,
      one_mul] using norm_inner_le_norm (𝕜 := ℂ) (fourierBasisFive j) x

private theorem amplitude_sub (x y : CoordinateFive) (r : GeometryRow) :
    geometryAmplitude (x - y) r = geometryAmplitude x r - geometryAmplitude y r := by
  simp only [geometryAmplitude_eq_inner, inner_sub_right]

private theorem norm_amplitude_smul (x : CoordinateFive) {c : ℂ} (hc : ‖c‖ = 1)
    (r : GeometryRow) : ‖geometryAmplitude (c • x) r‖ = ‖geometryAmplitude x r‖ := by
  simp only [geometryAmplitude_eq_inner, inner_smul_right, norm_mul, hc, one_mul]

private def tailReadout (s : Finset GeometryRow) (x : CoordinateFive) : EuclideanSpace ℂ s :=
  WithLp.toLp 2 (fun r => geometryAmplitude x r.val)

private theorem tailReadout_sub (s : Finset GeometryRow) (x y : CoordinateFive) :
    tailReadout s (x - y) = tailReadout s x - tailReadout s y := by
  apply PiLp.ext
  intro i
  exact amplitude_sub x y i.val

private theorem tailReadout_norm (s : Finset GeometryRow) (x : CoordinateFive) :
    ‖tailReadout s x‖ = Real.sqrt (maskMass (law x) s) := by
  rw [← Real.sqrt_sq (norm_nonneg (tailReadout s x)), EuclideanSpace.norm_sq_eq]
  congr 1
  simp only [maskMass, law_eq_amplitude]
  change (∑ i : s, ‖geometryAmplitude x i.val‖ ^ 2) = ∑ i ∈ s, ‖geometryAmplitude x i‖ ^ 2
  exact Finset.sum_coe_sort s (fun i => ‖geometryAmplitude x i‖ ^ 2)

private theorem norm_tailReadout_le (s : Finset GeometryRow) (x : CoordinateFive) :
    ‖tailReadout s x‖ ≤ Real.sqrt 2 * ‖x‖ := by
  have h : maskMass (law x) s ≤ ∑ i, law x i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => by
      rw [law_eq_amplitude]
      positivity
  rw [basisLaw_sum] at h
  rw [tailReadout_norm, show Real.sqrt 2 * ‖x‖ = Real.sqrt (2 * ‖x‖ ^ 2) by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg x)]]
  exact Real.sqrt_le_sqrt h

private theorem rankFour_top_tail_sum :
    maskMass (law (rankFourBasis rankFourTop)) rankFourTailRows = 1 - sharpSigma := by
  have hcard : rankFourTailRows.card = 4 := by decide
  unfold maskMass
  calc
    _ = ∑ _ ∈ rankFourTailRows, (1 - sharpSigma) / 4 :=
      Finset.sum_congr rfl (fun _ hi => rankFour_top_tail_mass hi)
    _ = _ := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      norm_num <;> ring

/-- Deficits and aligned distances, with pointwise and total amplitude bounds on the tail. -/
structure RankFourReference (x y : CoordinateFive) (s : Finset GeometryRow) where
  tail : Finset GeometryRow
  dx : ℝ
  dy : ℝ
  rx : ℝ
  ry : ℝ
  dx_nonneg : 0 ≤ dx
  dy_nonneg : 0 ≤ dy
  rx_nonneg : 0 ≤ rx
  ry_nonneg : 0 ≤ ry
  mass_diff : maskMass (law x) s - maskMass (law y) s = 1 + sharpSigma - dx - dy
  x_gap : (sharpSigma - sharpB) * rx ^ 2 ≤ 2 * dx
  y_gap : (1 - sharpSigma) * ry ^ 2 ≤ 2 * dy
  tail_x : Real.sqrt (1 - sharpSigma) - Real.sqrt 2 * rx ≤ Real.sqrt (maskMass (law x) tail)
  tail_rows : ∀ i ∈ tail, i ∉ s ∧
    Real.sqrt (law x i) ≤ Real.sqrt (1 - sharpSigma) / 2 + rx ∧
    Real.sqrt (2 / (7 + Real.sqrt 5)) - ry ≤ Real.sqrt (law y i)

private theorem rankFour_centered_reference (x y : CoordinateFive) (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) : Nonempty (RankFourReference x y centeredRankFour) := by
  obtain ⟨hdx, cx, hcx, hxgap⟩ := rankFour_top_gap x hx
  obtain ⟨hdy, cy, hcy, hygap⟩ := rankFour_kernel_gap y hy
  let x₀ := cx • rankFourBasis rankFourTop
  let y₀ := cy • rankFourBasis none
  have hlaw (v : CoordinateFive) {c : ℂ} (hc : ‖c‖ = 1) (i : GeometryRow) :
      law (c • v) i = law v i := by
    simp only [law_eq_amplitude, norm_amplitude_smul v hc]
  have hx₀ : maskMass (law x₀) rankFourTailRows = 1 - sharpSigma := by
    simpa only [x₀, maskMass, hlaw _ hcx] using rankFour_top_tail_sum
  refine ⟨⟨rankFourTailRows, 1 + sharpSigma - maskMass (law x) centeredRankFour,
    maskMass (law y) centeredRankFour, ‖x - x₀‖, ‖y - y₀‖, hdx, hdy,
    norm_nonneg _, norm_nonneg _, by ring, hxgap, hygap, ?_, ?_⟩⟩
  · have h : ‖tailReadout rankFourTailRows x₀‖ - ‖tailReadout rankFourTailRows x‖ ≤
        Real.sqrt 2 * ‖x - x₀‖ := calc
      _ ≤ ‖tailReadout rankFourTailRows x₀ - tailReadout rankFourTailRows x‖ :=
        norm_sub_norm_le _ _
      _ ≤ _ := by
        rw [← tailReadout_sub, norm_sub_rev x x₀]
        exact norm_tailReadout_le _ _
    rw [tailReadout_norm rankFourTailRows x₀, tailReadout_norm rankFourTailRows x, hx₀] at h
    linarith only [h]
  · intro i hi
    refine ⟨rankFourTailRows_not_mem hi, ?_, ?_⟩
    · have h₀ : Real.sqrt (law x₀ i) = Real.sqrt (1 - sharpSigma) / 2 := by
        dsimp only [x₀]
        rw [hlaw _ hcx]
        change Real.sqrt (law (centeredEigenbasis false (some (true, true))) i) = _
        rw [rankFour_top_tail_mass hi, Real.sqrt_div (by linarith only [sharp_sigma_bounds.2]),
          show Real.sqrt 4 = 2 by norm_num]
      have h : ‖geometryAmplitude x i‖ - ‖geometryAmplitude x₀ i‖ ≤ ‖x - x₀‖ := calc
        _ ≤ ‖geometryAmplitude x i - geometryAmplitude x₀ i‖ := norm_sub_norm_le _ _
        _ ≤ _ := by rw [← amplitude_sub]; exact norm_amplitude_le _ _
      rw [← sqrt_law x i, ← sqrt_law x₀ i, h₀] at h
      linarith only [h]
    · have h₀ : law y₀ i = 2 / (7 + Real.sqrt 5) := by
        dsimp only [y₀]
        rw [hlaw _ hcy, rankFour_kernel_tail_mass hi]
      have h : ‖geometryAmplitude y₀ i‖ - ‖geometryAmplitude y i‖ ≤ ‖y - y₀‖ := calc
        _ ≤ ‖geometryAmplitude y₀ i - geometryAmplitude y i‖ := norm_sub_norm_le _ _
        _ ≤ _ := by rw [← amplitude_sub, norm_sub_rev y y₀]; exact norm_amplitude_le _ _
      rw [← sqrt_law y₀ i, ← sqrt_law y i, h₀] at h
      linarith only [h]

/-- The affine isometry transports the reference rays, and its row phases preserve
all their amplitude bounds and the actual mask masses. -/
theorem rankFourReference_affine (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (u : (ZMod 5)ˣ) (a b : ZMod 5) :
    Nonempty (RankFourReference x y (centeredRankFour.map (affineRows u a b).toEmbedding)) := by
  let U := affineState u a b
  let e := affineRows u a b
  obtain ⟨x, rfl⟩ := U.surjective x
  obtain ⟨y, rfl⟩ := U.surjective y
  have hrow (v : CoordinateFive) (i : GeometryRow) : law (U v) (e i) = law v i := by
    simp only [law_eq_amplitude, U, e, geometryAmplitude_affine, norm_mul, norm_affineRowPhase, one_mul]
  have hmass (v : CoordinateFive) (s : Finset GeometryRow) :
      maskMass (law (U v)) (s.map e.toEmbedding) = maskMass (law v) s := by
    simp only [maskMass, Finset.sum_map, Equiv.toEmbedding_apply, hrow]
  obtain ⟨ref⟩ := rankFour_centered_reference x y (by simpa only [U.norm_map] using hx)
    (by simpa only [U.norm_map] using hy)
  refine ⟨⟨ref.tail.map e.toEmbedding, ref.dx, ref.dy, ref.rx, ref.ry, ref.dx_nonneg,
    ref.dy_nonneg, ref.rx_nonneg, ref.ry_nonneg, ?_, ref.x_gap, ref.y_gap, ?_, ?_⟩⟩
  · change maskMass (law (U x)) (centeredRankFour.map e.toEmbedding) -
      maskMass (law (U y)) (centeredRankFour.map e.toEmbedding) = _
    rw [hmass, hmass]
    exact ref.mass_diff
  · simpa only [hmass] using ref.tail_x
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨hjs, hjx, hjy⟩ := ref.tail_rows j hj
    refine ⟨?_, ?_, ?_⟩
    · change e j ∉ centeredRankFour.map e.toEmbedding
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hjs
    · simpa only [Equiv.toEmbedding_apply, hrow] using hjx
    · simpa only [Equiv.toEmbedding_apply, hrow] using hjy

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
