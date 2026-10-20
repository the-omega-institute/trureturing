/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-source coordinate monodromy of the actual corrected half-Fock Hahn field. -/

/- Classical twisted-lattice construction: Dong--Nagatomo math/9808088v1,
   section 3.2, pp.12--14; Bakalov--Kac math/0402315v1, (4.4), (4.23)--(4.38).
   Adapted from the preserved CorrectedField source; the canonical constructors
   remain in OriginalTranslation. Copyright (c) 2025 Kalle Kytölä;
   additional half-integer implementation copyright (c) 2026. Apache 2.0.
   Finite support architecture: VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4
   and PolynomialFock bfd9ff0f15397a4fb933f36d701a60d325d84b08. No novelty claim. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
import D5.S3.VertexAlgebra.LatticeInvolution

/-! Coordinate monodromy on every algebraic source and the full actual tensor module. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedMonodromy
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection LatticeInvolution
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private def coefficientLinear (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) :
    NativeField D hu →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) where
  toFun A := A.coeff e
  map_add' A B := by simp
  map_smul' c A := by simp

private theorem sign_square (n : ℕ) : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

private theorem jetShift_sign (D : LatticeData) (w : List (Index D)) :
    (-1 : ℂ) ^ jetShift D w = (-1 : ℂ) ^ w.length := by
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  induction w with
  | nil => simp [jetShift]
  | cons i w ih =>
    rw [jetShift, zpow_add₀ hn, zpow_add₀ hn,
      (even_two_mul (i.2 : ℤ)).neg_one_zpow, ih]
    simp [List.length_cons, pow_succ, mul_comm]

private theorem word_index_sign (D : LatticeData) (w : List (Index D))
    (m : ModeTuple D w) (e : ℤ) :
    (-1 : ℂ) ^ (e + 2 * modeSum D w m + jetShift D w) =
      (-1 : ℂ)^e * (-1 : ℂ)^w.length := by
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [zpow_add₀ hn, zpow_add₀ hn,
    (even_two_mul (modeSum D w m)).neg_one_zpow, jetShift_sign, mul_one]

private theorem flat_charge_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (m : ModeTuple D w) (e : ℤ) :
    flatCoefficient D hu (chargedField D hu (-a)) w m e =
      ((-1 : ℂ)^e * (-1 : ℂ)^w.length) •
        flatCoefficient D hu (chargedField D hu a) w m e := by
  rw [flatCoefficient_factorization, flatCoefficient_factorization]
  simp only [chargedField, HVertexOperator.coeff_of_coeff]
  rw [charged_coefficient_coordinate_monodromy, word_index_sign,
    mul_smul_comm, smul_mul_assoc]

private theorem word_charge_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (e : ℤ) :
    (chargedWordField D hu (-a) w).coeff e =
      ((-1 : ℂ)^e * (-1 : ℂ)^w.length) • (chargedWordField D hu a w).coeff e := by
  apply LinearMap.ext
  intro v
  simp only [chargedWordField, wordField_coefficient, LinearMap.smul_apply]
  rw [smul_finsum' _ (flatTerm_finite D hu (chargedField D hu a) w e v)]
  apply finsum_congr
  intro m
  change flatCoefficient D hu (chargedField D hu (-a)) w m e v = _
  rw [flat_charge_parity, LinearMap.smul_apply]
  rfl

/- proof_shape: normal_polynomial_coordinate_monodromy: content
   admission_basis: escape-witness
   escape_witness: Original charged coefficient monodromy and the odd jetShift
   contribute the word-length sign; sigma_monomial cancels it. Pointwise finsum
   uses the supplier's actual finite-support proof for every target vector. -/
theorem normal_polynomial_coordinate_monodromy (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ) :
    (polynomialField D hu (-a) (sigma D p)).coeff e =
      ((-1 : ℂ)^e) • (polynomialField D hu a p).coeff e := by
  let L := (coefficientLinear D hu e).comp
    ((polynomialField D hu (-a)).comp (sigmaLinear D))
  let R := ((-1 : ℂ)^e) • (coefficientLinear D hu e).comp (polynomialField D hu a)
  have h : L = R := by
    apply (basisMonomials (Index D) ℂ).ext
    intro d
    change (polynomialField D hu (-a) (sigma D (monomial d 1))).coeff e = _
    rw [sigma_monomial, map_smul, polynomialField_monomial_public]
    simp only [map_smul, Pi.smul_apply]
    change ((-1 : ℂ)^(occurrences D d).length) •
      (chargedWordField D hu (-a) (occurrences D d)).coeff e =
      ((-1 : ℂ)^e) • (polynomialField D hu a (monomial d 1)).coeff e
    rw [polynomialField_monomial_public, word_charge_parity, smul_smul]
    congr 1
    calc
      _ = ((-1 : ℂ)^e) *
          ((-1 : ℂ)^(occurrences D d).length * (-1 : ℂ)^(occurrences D d).length) := by ring
      _ = _ := by rw [sign_square, mul_one]
  exact LinearMap.congr_fun h p

/- The lift has no determinant or ground-module dependency. -/
private def correctionSigma (D : LatticeData) :
    CorrectionPolynomial D →ₐ[ℂ] CorrectionPolynomial D :=
  eval₂AlgHom ℂ (fun i => i.elim (X none) (fun j => -X (some j)))

@[simp] private theorem correctionSigma_C (D : LatticeData) (c : ℂ) :
    correctionSigma D (C c) = C c := by simp [correctionSigma]

@[simp] private theorem correctionSigma_none (D : LatticeData) :
    correctionSigma D (X none) = X none := by simp [correctionSigma]

@[simp] private theorem correctionSigma_some (D : LatticeData) (i : Index D) :
    correctionSigma D (X (some i)) = -X (some i) := by simp [correctionSigma]

private theorem correctionSigma_singleton (D : LatticeData) (a : Charge D) (i : Index D) :
    correctionSigma D (singletonPolynomial D a i) = -singletonPolynomial D (-a) i := by
  simp [singletonPolynomial, map_mul, map_pow, bilinear]

private theorem correctionSigma_pair (D : LatticeData) (i j : Index D) :
    correctionSigma D (pairPolynomial D i j) = pairPolynomial D i j := by
  simp [pairPolynomial, map_mul, map_pow]

private theorem correctionSigma_derivation (D : LatticeData) (i : Index D)
    (f : CorrectionPolynomial D) :
    correctionSigma D (pairDerivation D i f) =
      -pairDerivation D i (correctionSigma D f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg, neg_add]
  | mul_X f j hf =>
    cases j with
    | none =>
      have hz : pairDerivation D i (X none) = 0 := by
        simp [pairDerivation, mkDerivation_X]
      simp [Derivation.leibniz, smul_eq_mul, map_mul, hz, hf]
    | some j =>
      have hx : pairDerivation D i (X (some j)) = pairPolynomial D i j := by
        simp [pairDerivation, mkDerivation_X]
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hf, hx,
        correctionSigma_some, correctionSigma_pair, map_neg]
      ring

private theorem correctionSigma_insertion (D : LatticeData) (a : Charge D)
    (i : Index D) (f : CorrectionPolynomial D) :
    correctionSigma D (insertion D a i f) =
      -insertion D (-a) i (correctionSigma D f) := by
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_mul, correctionSigma_some,
    correctionSigma_singleton, correctionSigma_derivation]
  ring

private theorem correctionSigma_word (D : LatticeData) (a : Charge D)
    (w : List (Index D)) :
    correctionSigma D (correctionWord D a w) =
      ((-1 : ℂ)^w.length) • correctionWord D (-a) w := by
  induction w with
  | nil => simp [correctionWord]
  | cons i w ih =>
    rw [correctionWord, correctionSigma_insertion, ih, map_smul]
    simp [correctionWord, List.length_cons, pow_succ, neg_smul, smul_smul, mul_comm]

private theorem option_correctionSigma (D : LatticeData) (f : CorrectionPolynomial D) :
    optionEquivLeft ℂ (Index D) (correctionSigma D f) =
      Polynomial.map (sigma D) (optionEquivLeft ℂ (Index D) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg, Polynomial.map_add]
  | mul_X f j hf =>
    cases j <;> simp [map_mul, hf]

private theorem Corr_sigma_linear (D : LatticeData) (a : Charge D) :
    (Corr D (-a)).comp (sigmaLinear D) =
      (Finsupp.mapRange.linearMap (sigmaLinear D)).comp (Corr D a) := by
  apply (basisMonomials (Index D) ℂ).ext
  intro d
  apply Finsupp.ext
  intro s
  change Corr D (-a) (sigma D (monomial d 1)) s = sigma D (Corr D a (monomial d 1) s)
  rw [sigma_monomial, map_smul, Finsupp.smul_apply,
    Corr_monomial_enumeration D (-a) d (LatticeAllStateField.occurrences D d) (List.Perm.refl _),
    Corr_monomial_enumeration D a d (LatticeAllStateField.occurrences D d) (List.Perm.refl _)]
  have h := congrArg (fun f => (optionEquivLeft ℂ (Index D) f).coeff s)
    (correctionSigma_word D a (LatticeAllStateField.occurrences D d))
  rw [option_correctionSigma] at h
  change ((-1 : ℂ)^(LatticeAllStateField.occurrences D d).length) •
      ((optionEquivLeft ℂ (Index D))
        (correctionWord D (-a) (LatticeAllStateField.occurrences D d))).coeff s =
    sigma D (((optionEquivLeft ℂ (Index D))
      (correctionWord D a (LatticeAllStateField.occurrences D d))).coeff s)
  simpa only [map_smul, Polynomial.coeff_smul, Polynomial.coeff_map] using h.symm

/- proof_shape: Corr_sigma: bind-only
   consumer: correctedPolynomial_parity uses this full finite-support identity.
   The content is the shift-fixing insertion calculation in Corr_sigma_linear. -/
theorem Corr_sigma (D : LatticeData) (a : Charge D) (p : Oscillator D) :
    Corr D (-a) (sigma D p) =
      Finsupp.mapRange.linearMap (sigmaLinear D) (Corr D a p) := by
  exact LinearMap.congr_fun (Corr_sigma_linear D a) p

private theorem even_shift_sign (e : ℤ) (s : ℕ) :
    (-1 : ℂ)^(e + 2 * (s : ℤ)) = (-1 : ℂ)^e := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    (even_two_mul (s : ℤ)).neg_one_zpow, mul_one]

private theorem correctedSum_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) :
    (coefficientLinear D hu e).comp ((correctedSum D hu (-a)).comp
      (Finsupp.mapRange.linearMap (sigmaLinear D))) =
      ((-1 : ℂ)^e) • (coefficientLinear D hu e).comp (correctedSum D hu a) := by
  apply Finsupp.lhom_ext
  intro s p
  simp only [LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, correctedSum, Finsupp.lsum_single, LinearMap.smul_apply]
  change (shiftField D hu s (polynomialField D hu (-a) (sigma D p))).coeff e =
    ((-1 : ℂ)^e) • (shiftField D hu s (polynomialField D hu a p)).coeff e
  rw [shiftField_coefficient_public, shiftField_coefficient_public,
    normal_polynomial_coordinate_monodromy, even_shift_sign]

private theorem correctedPolynomial_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ) :
    (correctedPolynomial D hu (-a) (sigma D p)).coeff e =
      ((-1 : ℂ)^e) • (correctedPolynomial D hu a p).coeff e := by
  have hc := Corr_sigma D a p
  change coefficientLinear D hu e
    (correctedSum D hu (-a) (Corr D (-a) (sigma D p))) = _
  rw [hc]
  exact LinearMap.congr_fun (correctedSum_parity D hu a e) (Corr D a p)

/- proof_shape: correctedField_theta: content
   admission_basis: escape-witness
   escape_witness: Corr_sigma and normal polynomial parity are consumed in
   correctedSum_parity, using (-1)^(e+2s)=(-1)^e. Finite-charge linear-map
   extensionality then uses the original theta_single. No action on the target. -/
theorem correctedField_theta (D : LatticeData) (hu : IsUnit D.G.det)
    (u : Carrier D) (e : ℤ) :
    (correctedField D hu (theta D u)).coeff e =
      ((-1 : ℂ)^e) • (correctedField D hu u).coeff e := by
  have h : (coefficientLinear D hu e).comp
      ((correctedField D hu).comp (thetaLinear D)) =
      ((-1 : ℂ)^e) • (coefficientLinear D hu e).comp (correctedField D hu) := by
    apply Finsupp.lhom_ext
    intro a p
    simp only [LinearMap.comp_apply, theta_single, correctedField,
      Finsupp.lsum_single, LinearMap.smul_apply]
    exact correctedPolynomial_parity D hu a p e
  exact LinearMap.congr_fun h u

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
