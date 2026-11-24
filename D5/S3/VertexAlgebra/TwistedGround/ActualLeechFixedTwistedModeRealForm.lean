/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualLeechFixedTwistedModeRealForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualLeechFixedTwistedModeRealForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient conjugation of the actual corrected Leech field on the twisted sector. -/

import D5.S3.VertexAlgebra.Lattice.ActualCoefficientRealForm
import D5.S3.VertexAlgebra.TwistedGround.ActualLeechTwistedTensorRealForm

/-! The word and charge extensions follow the native decomposition in
`LatticeHalfFockParityField`. The correction recursion uses the real singleton
and pair coefficients of `LatticeHalfFockFiniteCorrection`. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator
open ComplexConjugate

namespace D5.S3.VertexAlgebra.TwistedGround.ActualLeechFixedTwistedModeRealForm

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (leechUnit)
open ActualLeechTwistedTensorRealForm
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open Lattice.ActualCoefficientRealForm (fixedKappa)
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField
open LatticeInvolution (FixedCarrier)
open MvPolynomial SourceBPZ.OriginalMatterHermitian

local notation "TwistedTensor" => ActualTensor leechData leechUnit

private theorem halfBinomial_conj (degree : ℕ) :
    conj (halfBinomial degree) = halfBinomial degree := by
  simp only [halfBinomial, map_div₀, map_prod, map_sub, map_neg, map_one,
    map_ofNat, map_natCast]

private theorem pairScalar_conj (first second : ℕ) :
    conj (pairScalar first second) = pairScalar first second := by
  simp only [pairScalar, map_div₀, map_mul, map_add, map_natCast, halfBinomial_conj]

private abbrev correctionConjugation (D : LatticeData) :
    CorrectionPolynomial D →+* CorrectionPolynomial D :=
  MvPolynomial.map (starRingEnd ℂ)

private theorem singletonPolynomial_conj (D : LatticeData) (a : Charge D) (i : Index D) :
    correctionConjugation D (singletonPolynomial D a i) = singletonPolynomial D a i := by
  simp only [singletonPolynomial, correctionConjugation, map_mul, map_pow,
    MvPolynomial.map_C, MvPolynomial.map_X, halfBinomial_conj, map_intCast]

private theorem pairPolynomial_conj (D : LatticeData) (i j : Index D) :
    correctionConjugation D (pairPolynomial D i j) = pairPolynomial D i j := by
  simp only [pairPolynomial, correctionConjugation, map_mul, map_pow,
    MvPolynomial.map_C, MvPolynomial.map_X, pairScalar_conj, map_intCast]

private theorem pairDerivation_conj (D : LatticeData) (i : Index D)
    (f : CorrectionPolynomial D) :
    correctionConjugation D (pairDerivation D i f) =
      pairDerivation D i (correctionConjugation D f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [correctionConjugation, MvPolynomial.map_C, MvPolynomial.derivation_C, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    have fixed_derivative : correctionConjugation D (pairDerivation D i (X j)) =
        pairDerivation D i (X j) := by
      cases j with
      | none => simp [pairDerivation, mkDerivation_X]
      | some j => simp only [pairDerivation_variable, pairPolynomial_conj]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hf,
      fixed_derivative, MvPolynomial.map_X]

private theorem correctionWord_conj (D : LatticeData) (a : Charge D) (w : List (Index D)) :
    correctionConjugation D (correctionWord D a w) = correctionWord D a w := by
  induction w with
  | nil => simp only [correctionWord, map_one]
  | cons i w ih =>
    simp only [correctionWord, insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, map_add, map_mul, MvPolynomial.map_X, singletonPolynomial_conj,
      pairDerivation_conj, ih]

private theorem optionEquivLeft_conj (D : LatticeData) (f : CorrectionPolynomial D) :
    optionEquivLeft ℂ (Index D) (correctionConjugation D f) =
      Polynomial.map (MvPolynomial.map (starRingEnd ℂ)) (optionEquivLeft ℂ (Index D) f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [correctionConjugation, MvPolynomial.map_C, optionEquivLeft_C, Polynomial.map_C]
  | add f g hf hg => simp only [map_add, Polynomial.map_add, hf, hg]
  | mul_X f j hf =>
    cases j <;>
      simp only [map_mul, Polynomial.map_mul, hf, MvPolynomial.map_X,
        optionEquivLeft_X_none, optionEquivLeft_X_some, Polynomial.map_X, Polynomial.map_C]

private theorem monomial_one_kappa (D : LatticeData) (d : Index D →₀ ℕ) :
    kappaOsc (monomial d 1 : Oscillator D) = monomial d 1 := by
  simp only [kappaOsc, MvPolynomial.map_monomial, map_one]

private theorem monomial_smul_one (D : LatticeData) (d : Index D →₀ ℕ) (c : ℂ) :
    (monomial d c : Oscillator D) = c • (monomial d 1 : Oscillator D) := by
  rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- The original finite correction commutes with conjugation in every grade,
with the charge and shift variable preserved. -/
theorem Corr_kappa (D : LatticeData) (a : Charge D) (p : Oscillator D) :
    Corr D a (kappaOsc p) =
      Finsupp.mapRange.addMonoidHom (MvPolynomial.map (starRingEnd ℂ)).toAddMonoidHom
        (Corr D a p) := by
  classical
  apply Finsupp.ext
  intro s
  change Corr D a (kappaOsc p) s = kappaOsc (Corr D a p s)
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [kappaOsc_add, map_add, Finsupp.add_apply, hp, hq]
  | monomial d c =>
    rw [monomial_smul_one D d c]
    simp only [kappaOsc_smul, map_smul, Finsupp.smul_apply]
    apply congrArg (fun q : Oscillator D => conj c • q)
    rw [monomial_one_kappa, Corr_monomial_enumeration D a d
      (LatticeAllStateField.occurrences D d) (List.Perm.refl _)]
    let polynomial := optionEquivLeft ℂ (Index D)
      (correctionWord D a (LatticeAllStateField.occurrences D d))
    change polynomial.coeff s = kappaOsc (polynomial.coeff s)
    have fixed_polynomial :
        Polynomial.map (MvPolynomial.map (starRingEnd ℂ)) polynomial = polynomial := by
      dsimp only [polynomial]
      rw [← optionEquivLeft_conj, correctionWord_conj]
    simpa only [Polynomial.coeff_map, kappaOsc] using
      (congrArg (fun f : Polynomial (Oscillator D) => f.coeff s) fixed_polynomial).symm

private theorem halfCurrent_kappa (D : LatticeData) (i : Fin D.rank) (j : ℤ)
    (p : Oscillator D) :
    kappaOsc (LatticeHalfFock.current D i j p) = LatticeHalfFock.current D i j (kappaOsc p) := by
  unfold LatticeHalfFock.current
  split_ifs
  · simp only [LinearMap.mulLeft_apply, kappaOsc_mul, kappaOsc_X]
  · have frequency_conj : conj (LatticeHalfFock.frequency j) = LatticeHalfFock.frequency j := by
      simp only [LatticeHalfFock.frequency, map_add, map_div₀, map_intCast, map_one, map_ofNat]
    simp only [LinearMap.smul_apply, kappaOsc_smul, frequency_conj, kappaOsc_annihilate]

private theorem jetCurrent_kappa (i : Index leechData) (j : ℤ) (x : TwistedTensor) :
    tensorConjugation (jetCurrent leechData leechUnit i j x) =
      jetCurrent leechData leechUnit i j (tensorConjugation x) := by
  have jetScalar_conj : conj (jetScalar i.2 j) = jetScalar i.2 j := by
    simp only [jetScalar, map_div₀, map_prod, map_sub, map_neg, map_intCast,
      map_natCast, map_ofNat]
  induction x using TensorProduct.inductionOn with
  | tmul p t =>
    simp only [jetCurrent, LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
      LinearMap.smul_apply, map_smulₛₗ, TensorProduct.map_tmul, LinearMap.id_apply,
      tensorConjugation_tmul, jetScalar_conj, halfCurrent_kappa]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem flatCoefficient_kappa (a : Charge leechData) (w : List (Index leechData))
    (m : ModeTuple leechData w) (e : ℤ) (x : TwistedTensor) :
    tensorConjugation (flatCoefficient leechData leechUnit
        (chargedField leechData leechUnit a) w m e x) =
      flatCoefficient leechData leechUnit (chargedField leechData leechUnit a) w m e
        (tensorConjugation x) := by
  induction w generalizing e x with
  | nil =>
    simpa only [flatCoefficient, chargedField, HVertexOperator.coeff_of_coeff] using
      tensorConjugation_chargedCoefficient a e x
  | cons i w ih =>
    rcases m with ⟨j, m⟩
    by_cases hj : j < 0
    · simp only [flatCoefficient, ite_eq_left hj, Module.End.mul_apply]
      rw [jetCurrent_kappa, ih]
    · simp only [flatCoefficient, ite_eq_right hj, Module.End.mul_apply]
      rw [ih, jetCurrent_kappa]

/-- The actual normal word coefficient commutes with twisted conjugation. -/
theorem wordField_kappa (a : Charge leechData) (w : List (Index leechData))
    (e : ℤ) (x : TwistedTensor) :
    tensorConjugation ((wordField leechData leechUnit
        (chargedField leechData leechUnit a) w).coeff e x) =
      (wordField leechData leechUnit (chargedField leechData leechUnit a) w).coeff e
        (tensorConjugation x) := by
  rw [wordField_coefficient, wordField_coefficient,
    map_finsum _ (flatTerm_finite leechData leechUnit
      (chargedField leechData leechUnit a) w e x)]
  apply finsum_congr
  intro m
  exact flatCoefficient_kappa a w m e x

private theorem polynomialField_kappa (a : Charge leechData) (p : Oscillator leechData)
    (e : ℤ) (x : TwistedTensor) :
    tensorConjugation ((polynomialField leechData leechUnit a p).coeff e x) =
      (polynomialField leechData leechUnit a (kappaOsc p)).coeff e (tensorConjugation x) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [kappaOsc_add, map_add, Pi.add_apply, LinearMap.add_apply, hp, hq]
  | monomial d c =>
    rw [monomial_smul_one leechData d c]
    simp only [kappaOsc_smul, monomial_one_kappa, map_smul, Pi.smul_apply, LinearMap.smul_apply,
      map_smulₛₗ, polynomialField_monomial_public, wordField_kappa]

private theorem correctedSum_kappa (a : Charge leechData) (v : ℕ →₀ Oscillator leechData)
    (e : ℤ) (x : TwistedTensor) :
    tensorConjugation ((correctedSum leechData leechUnit a v).coeff e x) =
      (correctedSum leechData leechUnit a
        (Finsupp.mapRange.addMonoidHom (MvPolynomial.map (starRingEnd ℂ)).toAddMonoidHom v)).coeff e
          (tensorConjugation x) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hv, hw]
  | single s p =>
    have single_conj :
        Finsupp.mapRange.addMonoidHom (MvPolynomial.map (starRingEnd ℂ)).toAddMonoidHom
          (Finsupp.single s p) = Finsupp.single s (kappaOsc p) :=
      Finsupp.mapRange_single (hf := map_zero _)
    simp only [single_conj, correctedSum, Finsupp.lsum_single, LinearMap.comp_apply]
    rw [shiftField_coefficient_public, shiftField_coefficient_public]
    exact polynomialField_kappa a p (e + 2 * (s : ℤ)) x

private theorem correctedPolynomial_kappa (a : Charge leechData) (p : Oscillator leechData)
    (e : ℤ) (x : TwistedTensor) :
    tensorConjugation ((correctedPolynomial leechData leechUnit a p).coeff e x) =
      (correctedPolynomial leechData leechUnit a (kappaOsc p)).coeff e (tensorConjugation x) := by
  simp only [correctedPolynomial, LinearMap.comp_apply, Corr_kappa]
  exact correctedSum_kappa a (Corr leechData a p) e x

/-- Covariance of each literal corrected coefficient on the full twisted tensor
space, for every finite-charge lattice source. -/
theorem correctedField_kappa (a : Carrier leechData) (e : ℤ) (x : TwistedTensor) :
    tensorConjugation ((correctedField leechData leechUnit a).coeff e x) =
      (correctedField leechData leechUnit (kappaCarrier a)).coeff e (tensorConjugation x) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [kappaCarrier_add, map_add, Pi.add_apply, LinearMap.add_apply, ha, hb]
  | single a p =>
    simp only [kappaCarrier_single, correctedField, Finsupp.lsum_single]
    exact correctedPolynomial_kappa a p e x

/-- Conjugation of the fixed-to-twisted block in every integral normalized mode. -/
theorem fixedParitySlice_kappa (a : FixedCarrier leechData) (n : ℤ)
    (x : paritySpace leechData leechUnit (-1)) :
    negativeConjugation (((fixedParitySlice leechData leechUnit (-1) a)[[n]]) x) =
      ((fixedParitySlice leechData leechUnit (-1) (fixedKappa leechData a))[[n]])
        (negativeConjugation x) := by
  apply Subtype.ext
  simpa only [fixedParitySlice, VertexOperator.ncoeff_of_coeff,
    negativeConjugation, LinearMap.coe_restrict_apply, fixedKappa] using
      correctedField_kappa a.val (2 * (-n - 1)) (x : TwistedTensor)

end D5.S3.VertexAlgebra.TwistedGround.ActualLeechFixedTwistedModeRealForm
