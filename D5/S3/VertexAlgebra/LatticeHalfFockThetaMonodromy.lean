/- GID: D5/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockThetaMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite corrections and physical normal words yield all-state theta monodromy. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
import D5.S3.VertexAlgebra.LatticeInvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField
open LatticeHalfFockAllStateField LatticeHalfFockChargedMonodromy
open LatticeInvolution MvPolynomial
open scoped BigOperators

noncomputable section

private def sigmaHat (D : LatticeData) : CorrectionPolynomial D →+* CorrectionPolynomial D :=
  eval₂Hom C (fun coordinate => coordinate.elim (X none) (fun index => -X (some index)))

private theorem sigmaHat_C (D : LatticeData) (scalar : ℂ) :
    sigmaHat D (C scalar) = C scalar := by simp [sigmaHat]

private theorem sigmaHat_none (D : LatticeData) :
    sigmaHat D (X none) = X none := by simp [sigmaHat]

private theorem sigmaHat_some (D : LatticeData) (index : Index D) :
    sigmaHat D (X (some index)) = -X (some index) := by simp [sigmaHat]

private theorem singleton_neg (D : LatticeData) (charge : Charge D) (index : Index D) :
    singletonPolynomial D (-charge) index = -singletonPolynomial D charge index := by
  simp [singletonPolynomial, bilinear, Finset.sum_neg_distrib]

private theorem sigmaHat_singleton (D : LatticeData) (charge : Charge D) (index : Index D) :
    sigmaHat D (singletonPolynomial D charge index) = singletonPolynomial D charge index := by
  simp only [singletonPolynomial, map_mul, map_pow, sigmaHat_C, sigmaHat_none]

private theorem sigmaHat_pair (D : LatticeData) (first second : Index D) :
    sigmaHat D (pairPolynomial D first second) = pairPolynomial D first second := by
  simp only [pairPolynomial, map_mul, map_pow, sigmaHat_C, sigmaHat_none]

private theorem derivation_anticommutes (D : LatticeData) (index : Index D)
    (polynomial : CorrectionPolynomial D) :
    sigmaHat D (pairDerivation D index polynomial) =
      -pairDerivation D index (sigmaHat D polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [sigmaHat_C]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof, neg_add]
  | mul_X polynomial coordinate inductionProof =>
    cases coordinate with
    | none =>
      have variableLaw : pairDerivation D index (X none) = 0 := by
        simp [pairDerivation, mkDerivation_X]
      simp only [Derivation.leibniz, smul_eq_mul, map_mul,
        sigmaHat_none, variableLaw, mul_zero, zero_add,
        inductionProof, mul_neg]
    | some other =>
      have variableLaw : pairDerivation D index (X (some other)) =
          pairPolynomial D index other := by
        simp [pairDerivation, mkDerivation_X]
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        sigmaHat_some, map_neg, variableLaw, sigmaHat_pair,
        inductionProof, neg_mul, mul_neg, neg_add, neg_neg]

private theorem insertion_sign (D : LatticeData) (charge : Charge D) (index : Index D)
    (polynomial : CorrectionPolynomial D) :
    sigmaHat D (insertion D charge index polynomial) =
      -insertion D (-charge) index (sigmaHat D polynomial) := by
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_mul, sigmaHat_some, sigmaHat_singleton,
    singleton_neg, derivation_anticommutes]
  ring

private theorem correctionWord_sign (D : LatticeData) (charge : Charge D)
    (word : List (Index D)) :
    correctionWord D (-charge) word =
      ((-1 : ℂ) ^ word.length) • sigmaHat D (correctionWord D charge word) := by
  induction word with
  | nil => simp [correctionWord]
  | cons index tail inductionProof =>
    simp only [correctionWord, List.length_cons, inductionProof, map_smul,
      insertion_sign, pow_succ, mul_smul, neg_one_smul]
    simp only [neg_neg]

private theorem option_sign (D : LatticeData) (polynomial : CorrectionPolynomial D) :
    optionEquivLeft ℂ (Index D) (sigmaHat D polynomial) =
      Polynomial.map (sigma D) (optionEquivLeft ℂ (Index D) polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [sigmaHat_C, optionEquivLeft_C]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof, Polynomial.map_add]
  | mul_X polynomial coordinate inductionProof =>
    cases coordinate with
    | none =>
      simp only [map_mul, sigmaHat_none, optionEquivLeft_X_none, inductionProof,
        Polynomial.map_mul, Polynomial.map_X]
    | some index =>
      simp only [map_mul, sigmaHat_some, map_neg, optionEquivLeft_X_some,
        inductionProof, Polynomial.map_mul, Polynomial.map_C, sigma_X]

private theorem shift_sign (D : LatticeData) (polynomial : CorrectionPolynomial D)
    (shift : ℕ) :
    shiftCoefficients D (optionEquivLeft ℂ (Index D) (sigmaHat D polynomial)) shift =
      sigma D (shiftCoefficients D (optionEquivLeft ℂ (Index D) polynomial) shift) := by
  rw [option_sign]
  change (Polynomial.map (sigma D) (optionEquivLeft ℂ (Index D) polynomial)).coeff shift = _
  exact Polynomial.coeff_map _ _

private theorem Corr_sign (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (shift : ℕ) :
    Corr D (-charge) (sigma D polynomial) shift = sigma D (Corr D charge polynomial shift) := by
  induction polynomial using MvPolynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [map_add, Finsupp.add_apply, firstProof, secondProof]
  | monomial exponent scalar =>
    have monomialScalar : monomial exponent scalar = scalar • monomial exponent (1 : ℂ) := by
      simp [MvPolynomial.smul_monomial]
    rw [monomialScalar]
    simp only [sigma_smul, map_smul, Finsupp.smul_apply]
    congr 1
    rw [sigma_monomial, map_smul, Finsupp.smul_apply,
      Corr_monomial_enumeration D (-charge) exponent _ (List.Perm.refl _),
      Corr_monomial_enumeration D charge exponent _ (List.Perm.refl _), correctionWord_sign,
      map_smul, map_smul, Finsupp.smul_apply, shift_sign]
    rw [smul_smul]
    have square : ((-1 : ℂ) ^ (LatticeAllStateField.occurrences D exponent).length) *
        ((-1 : ℂ) ^ (LatticeAllStateField.occurrences D exponent).length) = 1 := by
      rw [← pow_add, ← two_mul]
      exact (even_two_mul _).neg_one_pow
    rw [square, one_smul]

private theorem sign_even_shift (exponent offset : ℤ) :
    (-1 : ℂ) ^ (exponent + 2 * offset) = (-1 : ℂ) ^ exponent := by
  rw [zpow_add₀ (by norm_num), (even_two_mul offset).neg_one_zpow, mul_one]

private theorem jetShift_length (D : LatticeData) (word : List (Index D)) :
    jetShift D word = (word.length : ℤ) + 2 * (wordWeight D word : ℤ) := by
  induction word with
  | nil => simp [jetShift, wordWeight]
  | cons index tail inductionProof =>
    simp only [jetShift, wordWeight, List.map_cons, List.sum_cons, sourceWeight,
      List.length_cons, Nat.cast_add, Nat.cast_one, inductionProof]
    ring

private theorem normalWord_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (exponent : ℤ) :
    (normalWord D hu (-charge) word).coeff exponent =
      ((-1 : ℂ) ^ (exponent + (word.length : ℤ))) •
        (normalWord D hu charge word).coeff exponent := by
  apply LinearMap.ext
  intro vector
  rw [normalWord_flattened, LinearMap.smul_apply, normalWord_flattened,
    smul_finsum' _ (flatTerm_finite D hu (chargedField D hu charge) word exponent vector)]
  apply finsum_congr
  intro modes
  simp only [flatTerm, flatCoefficient_factorization, chargedField,
    HVertexOperator.coeff_of_coeff]
  rw [charged_coefficient_coordinate_monodromy]
  have shift : exponent + 2 * modeSum D word modes + jetShift D word =
      exponent + (word.length : ℤ) +
        2 * (modeSum D word modes + (wordWeight D word : ℤ)) := by
    rw [jetShift_length]
    ring
  rw [shift, sign_even_shift]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul]

private theorem normalPolynomial_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (exponent : ℤ) :
    (normalPolynomial D hu (-charge) (sigma D polynomial)).coeff exponent =
      ((-1 : ℂ) ^ exponent) • (normalPolynomial D hu charge polynomial).coeff exponent := by
  induction polynomial using MvPolynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [map_add, Pi.add_apply, firstProof, secondProof, smul_add]
  | monomial sourceExponent scalar =>
    have monomialScalar : monomial sourceExponent scalar =
        scalar • monomial sourceExponent (1 : ℂ) := by simp [MvPolynomial.smul_monomial]
    rw [monomialScalar, sigma_smul]
    simp only [map_smul, Pi.smul_apply]
    rw [smul_comm ((-1 : ℂ) ^ exponent) scalar]
    congr 1
    rw [sigma_monomial, map_smul]
    simp only [map_smul, Pi.smul_apply]
    rw [normalPolynomial_monomial_enumeration D hu (-charge) sourceExponent _ (List.Perm.refl _),
      normalPolynomial_monomial_enumeration D hu charge sourceExponent _ (List.Perm.refl _),
      normalWord_sign, smul_smul]
    congr 1
    rw [zpow_add₀ (by norm_num), zpow_natCast]
    have square : ((-1 : ℂ) ^ (LatticeAllStateField.occurrences D sourceExponent).length) *
        ((-1 : ℂ) ^ (LatticeAllStateField.occurrences D sourceExponent).length) = 1 := by
      rw [← pow_add, ← two_mul]
      exact (even_two_mul _).neg_one_pow
    calc
      _ = ((-1 : ℂ) ^ exponent) *
          (((-1 : ℂ) ^ (LatticeAllStateField.occurrences D sourceExponent).length) *
            ((-1 : ℂ) ^ (LatticeAllStateField.occurrences D sourceExponent).length)) := by ring
      _ = _ := by rw [square, mul_one]

private theorem correction_sum_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (correction : ℕ →₀ Oscillator D) (exponent : ℤ) :
    (Finsupp.lsum ℂ (fun shift : ℕ =>
        (shiftLinear D hu shift).comp (normalPolynomial D hu (-charge)))
      (Finsupp.mapRange.linearMap (sigmaLinear D) correction)).coeff exponent =
      ((-1 : ℂ) ^ exponent) •
        (Finsupp.lsum ℂ (fun shift : ℕ =>
          (shiftLinear D hu shift).comp (normalPolynomial D hu charge))
            correction).coeff exponent := by
  induction correction using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, Pi.add_apply, firstProof, secondProof, smul_add]
  | single shift polynomial =>
    change (Finsupp.lsum ℂ (fun shift : ℕ =>
        (shiftLinear D hu shift).comp (normalPolynomial D hu (-charge)))
      (Finsupp.mapRange (sigma D) (map_zero _)
        (Finsupp.single shift polynomial))).coeff exponent = _
    rw [Finsupp.mapRange_single, Finsupp.lsum_single, Finsupp.lsum_single]
    simp only [LinearMap.comp_apply]
    change (shiftField D hu shift (normalPolynomial D hu (-charge) (sigma D polynomial))).coeff
      exponent = ((-1 : ℂ) ^ exponent) •
        (shiftField D hu shift (normalPolynomial D hu charge polynomial)).coeff exponent
    simp only [shiftField, HVertexOperator.coeff_of_coeff]
    rw [normalPolynomial_sign, sign_even_shift]

private theorem correctedPolynomial_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (exponent : ℤ) :
    (correctedPolynomial D hu (-charge) (sigma D polynomial)).coeff exponent =
      ((-1 : ℂ) ^ exponent) • (correctedPolynomial D hu charge polynomial).coeff exponent := by
  have correction : Corr D (-charge) (sigma D polynomial) =
      Finsupp.mapRange.linearMap (sigmaLinear D) (Corr D charge polynomial) := by
    apply Finsupp.ext
    intro shift
    exact Corr_sign D charge polynomial shift
  simp only [correctedPolynomial, LinearMap.comp_apply]
  rw [correction]
  exact correction_sum_sign D hu charge (Corr D charge polynomial) exponent

theorem Ytw_theta (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (exponent : ℤ) :
    (Ytw D hu (theta D source)).coeff exponent =
      ((-1 : ℂ) ^ exponent) • (Ytw D hu source).coeff exponent := by
  induction source using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, Pi.add_apply, firstProof, secondProof, smul_add]
  | single charge polynomial =>
    change (Ytw D hu (thetaLinear D (Finsupp.single charge polynomial))).coeff exponent = _
    rw [theta_single]
    simp only [Ytw, Finsupp.lsum_single]
    exact correctedPolynomial_sign D hu charge polynomial exponent

theorem Ytw_coefficient_selection (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (eigenvalue : ℂ) (eigenstate : theta D source = eigenvalue • source)
    (exponent : ℤ) (mismatch : eigenvalue ≠ (-1 : ℂ) ^ exponent) :
    (Ytw D hu source).coeff exponent = 0 := by
  have covariance := Ytw_theta D hu source exponent
  rw [eigenstate] at covariance
  simp only [map_smul, Pi.smul_apply] at covariance
  have annihilation : (eigenvalue - (-1 : ℂ) ^ exponent) •
      (Ytw D hu source).coeff exponent = 0 := by
    rw [sub_smul, covariance, sub_self]
  exact (smul_eq_zero.mp annihilation).resolve_left (sub_ne_zero.mpr mismatch)

theorem Ytw_even_odd_selection (D : LatticeData) (hu : IsUnit D.G.det) :
    (∀ (source : Carrier D), theta D source = source →
      ∀ exponent : ℤ, Odd exponent → (Ytw D hu source).coeff exponent = 0) ∧
    (∀ (source : Carrier D), theta D source = -source →
      ∀ exponent : ℤ, Even exponent → (Ytw D hu source).coeff exponent = 0) := by
  constructor
  · intro source eigenstate exponent oddExponent
    apply Ytw_coefficient_selection D hu source 1 (by simpa using eigenstate) exponent
    rw [oddExponent.neg_one_zpow]
    norm_num
  · intro source eigenstate exponent evenExponent
    apply Ytw_coefficient_selection D hu source (-1) (by simpa using eigenstate) exponent
    rw [evenExponent.neg_one_zpow]
    norm_num

theorem Ytw_physical_mode_selection (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (alpha beta : ℤ) (alphaSector : alpha = 0 ∨ alpha = 1)
    (betaSector : beta = 0 ∨ beta = 1)
    (eigenstate : theta D source = ((-1 : ℂ) ^ alpha) • source)
    (different : alpha ≠ beta) (mode : ℤ) :
    (Ytw D hu source).coeff (-2 * mode - beta - 2) = 0 := by
  rcases alphaSector with rfl | rfl <;> rcases betaSector with rfl | rfl
  · exact (different rfl).elim
  · apply (Ytw_even_odd_selection D hu).1 source (by simpa using eigenstate)
    exact ⟨-mode - 2, by ring⟩
  · apply (Ytw_even_odd_selection D hu).2 source (by simpa using eigenstate)
    exact ⟨-mode - 1, by ring⟩
  · exact (different rfl).elim

#print axioms Ytw_theta
#print axioms Ytw_coefficient_selection
#print axioms Ytw_even_odd_selection
#print axioms Ytw_physical_mode_selection

end
end D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy
