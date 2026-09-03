/- GID: D5/S3/Weil/Budget/CrossScaleGramIdentity
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/CrossScaleGramIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify transported Cayley moments with the Gram matrix of rational features. -/

import D5.S3.Weil.Budget.PositiveCayleyScaleTransport
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * D5 body-shape searches for cross-scale Gram, Crofoot--Malmquist,
     weighted disk-automorphism features, and their conjugate products found
     the canonical scale-change and positive transport primitives, but no
     theorem stating this Gram identity.
   * Pinned Mathlib supplies Bochner `integral_map`, integration against
     `withDensity`, integer-power subtraction, and complex conjugation laws,
     but no Crofoot--Malmquist or cross-scale Gram theorem.
   * GitHub Lean code searches for `Crofoot` and `Malmquist` returned no hits;
     the unrelated `weighted composition` hits contain no measure identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace D5.S3.Weil.Budget.CrossScaleGramIdentity

open CayleyScaleChange PositiveCayleyScaleTransport

/-- The scale-`b` integer moment is the scale-`a` Gram pairing of the
explicit rational features induced by the Cayley disk automorphism. -/
theorem cross_scale_gram_identity
    (source : Measure Real) (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (j k : Nat) :
    let r := scaleChangeParameter a b
    let moment := fun (scale : Real) (n : Int) =>
      ∫ z : Complex, z ^ n ∂cayleySpectralMeasure source scale
    let feature := fun (index : Nat) (z : Complex) =>
      (((Real.sqrt (1 - r ^ 2) : Real) : Complex) /
          (1 + (r : Complex) * z)) *
        realDiskAutomorphism r z ^ index
    moment b ((j : Int) - (k : Int)) =
      ((a / b : Real) : Complex) *
        ∫ z : Complex, feature j z * star (feature k z)
          ∂cayleySpectralMeasure source a := by
  dsimp only
  let r : Real := scaleChangeParameter a b
  have hr : |r| < 1 := by
    dsimp only [r, scaleChangeParameter]
    have hab : 0 < a + b := add_pos ha hb
    rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hab]
      linarith
    · rw [div_lt_iff₀ hab]
      linarith
  have hrsq : 0 <= 1 - r ^ 2 := by
    rw [abs_lt] at hr
    nlinarith
  have hsqrtSq : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
    Real.sq_sqrt hrsq
  have hscale : (a / b) * (1 - r ^ 2) = (1 + r) ^ 2 := by
    dsimp only [r, scaleChangeParameter]
    field_simp [ne_of_gt (add_pos ha hb), ne_of_gt hb]
    ring
  have hphiMeas : Measurable (realDiskAutomorphism (scaleChangeParameter a b)) := by
    unfold realDiskAutomorphism
    fun_prop
  have hweightMeas : Measurable fun z : Complex =>
      ENNReal.ofReal (scaleTransportWeight a b z) := by
    unfold scaleTransportWeight
    fun_prop
  rw [positive_cayley_scale_transport source a b ha hb]
  rw [MeasureTheory.integral_map hphiMeas.aemeasurable (by fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul
    hweightMeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  unfold cayleySpectralMeasure
  have hleftMeas : Measurable fun z : Complex =>
      (ENNReal.ofReal (scaleTransportWeight a b z)).toReal •
        realDiskAutomorphism (scaleChangeParameter a b) z ^
          ((j : Int) - (k : Int)) := by
    unfold realDiskAutomorphism scaleTransportWeight
    fun_prop
  have hrightMeas : Measurable fun z : Complex =>
      ((a / b : Real) : Complex) *
        ((((Real.sqrt (1 - scaleChangeParameter a b ^ 2) : Real) : Complex) /
              (1 + (scaleChangeParameter a b : Complex) * z)) *
            realDiskAutomorphism (scaleChangeParameter a b) z ^ j *
          star
            ((((Real.sqrt (1 - scaleChangeParameter a b ^ 2) : Real) : Complex) /
                (1 + (scaleChangeParameter a b : Complex) * z)) *
              realDiskAutomorphism (scaleChangeParameter a b) z ^ k)) := by
    unfold realDiskAutomorphism
    fun_prop
  apply (ae_map_iff (by
    unfold cayleyCoordinate
    fun_prop) (measurableSet_eq_fun hleftMeas hrightMeas)).2
  filter_upwards with spectral
  have hca : ‖cayleyCoordinate a spectral‖ = 1 := by
    unfold cayleyCoordinate
    rw [norm_div]
    have hden : ‖(spectral : Complex) - Complex.I * (a : Complex)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hnorm :
        ‖(spectral : Complex) + Complex.I * (a : Complex)‖ =
          ‖(spectral : Complex) - Complex.I * (a : Complex)‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
    rw [hnorm, div_self hden]
  have hcb : ‖cayleyCoordinate b spectral‖ = 1 := by
    unfold cayleyCoordinate
    rw [norm_div]
    have hden : ‖(spectral : Complex) - Complex.I * (b : Complex)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hnorm :
        ‖(spectral : Complex) + Complex.I * (b : Complex)‖ =
          ‖(spectral : Complex) - Complex.I * (b : Complex)‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
    rw [hnorm, div_self hden]
  have hphi := cayley_scale_change a b spectral ha hb
  have hcaStar : (starRingEnd Complex) (cayleyCoordinate a spectral) =
      (cayleyCoordinate a spectral)⁻¹ :=
    (Complex.inv_eq_conj hca).symm
  have hcbStar : (starRingEnd Complex) (cayleyCoordinate b spectral) =
      (cayleyCoordinate b spectral)⁻¹ :=
    (Complex.inv_eq_conj hcb).symm
  have hcaNe : cayleyCoordinate a spectral ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hca]; norm_num)
  have hcbNe : cayleyCoordinate b spectral ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hcb]; norm_num)
  have hdenNe : 1 + (r : Complex) * cayleyCoordinate a spectral ≠ 0 := by
    intro h
    have hnorm := congrArg norm (eq_neg_of_add_eq_zero_left h)
    simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, hca,
      mul_one, norm_one] at hnorm
    linarith
  rw [ENNReal.toReal_ofReal (by
    unfold scaleTransportWeight
    exact div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))]
  rw [Complex.real_smul]
  rw [show realDiskAutomorphism r (cayleyCoordinate a spectral) =
      cayleyCoordinate b spectral by simpa only [r] using hphi.symm]
  rw [zpow_natCast_sub_natCast₀ hcbNe]
  simp only [map_mul, map_div₀, map_pow, Complex.star_def,
    Complex.conj_ofReal, hcbStar]
  unfold scaleTransportWeight
  change
    ((((1 + r) ^ 2 / Complex.normSq
          (1 + (r : Complex) * cayleyCoordinate a spectral) : Real) : Complex) *
        (cayleyCoordinate b spectral ^ j / cayleyCoordinate b spectral ^ k)) =
      ((a / b : Real) : Complex) *
        (((Real.sqrt (1 - r ^ 2) : Real) : Complex) /
              (1 + (r : Complex) * cayleyCoordinate a spectral) *
            cayleyCoordinate b spectral ^ j *
          (((Real.sqrt (1 - r ^ 2) : Real) : Complex) /
              (starRingEnd Complex) (1 + (r : Complex) * cayleyCoordinate a spectral) *
            (cayleyCoordinate b spectral)⁻¹ ^ k))
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_one]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_add, map_one, map_mul, Complex.conj_ofReal, hcaStar]
  have hdenStarNe :
      1 + (r : Complex) * (cayleyCoordinate a spectral)⁻¹ ≠ 0 := by
    have hstar :
        (starRingEnd Complex)
            (1 + (r : Complex) * cayleyCoordinate a spectral) ≠ 0 := by
      simpa only [map_zero] using
        (starRingEnd Complex).injective.ne hdenNe
    simpa only [map_add, map_one, map_mul, Complex.conj_ofReal, hcaStar]
      using hstar
  have hcaAddNe : cayleyCoordinate a spectral + (r : Complex) ≠ 0 := by
    intro h
    apply hdenStarNe
    field_simp [hcaNe]
    simpa only [add_comm, mul_zero] using h
  field_simp [hdenNe, hdenStarNe, hcaAddNe, hcaNe, hcbNe]
  rw [show (Real.sqrt (1 - r ^ 2) : Complex) ^ 2 =
      (1 - r ^ 2 : Real) by
    norm_cast]
  simp only [one_div, inv_pow]
  have hcancel :
      cayleyCoordinate b spectral ^ k * ((a / b : Real) : Complex) *
          ((1 - r ^ 2 : Real) : Complex) *
          (cayleyCoordinate b spectral ^ k)⁻¹ =
        ((a / b : Real) : Complex) * ((1 - r ^ 2 : Real) : Complex) := by
    field_simp [pow_ne_zero k hcbNe]
  rw [hcancel]
  exact_mod_cast hscale.symm

#print axioms cross_scale_gram_identity

end D5.S3.Weil.Budget.CrossScaleGramIdentity
