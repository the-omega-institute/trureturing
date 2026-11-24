/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualLeechTwistedTensorRealForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualLeechTwistedTensorRealForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient conjugation on the actual Leech twisted tensor and negative eigenspace. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
import D5.S3.VertexAlgebra.TwistedGround.ActualLeechGroundConjugation

/-! The actual twisted tensor has a conjugation compatible with parity,
its native pairing, and its charged Laurent coefficients. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct
open ComplexConjugate

namespace D5.S3.VertexAlgebra.TwistedGround.ActualLeechTwistedTensorRealForm

open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open ActualLeechGroundConjugation (leechGroundConjugation)
open ChargeHermitian (chargeForm charge_form_hermitian)
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients
open LatticeHalfFockParityT (actualParity)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeInvolution (sigma)
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open SignedOscillatorWick
open SourceBPZ.OriginalMatterHermitian

open private selectedGroundPairing actualForm_tmul from
  D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open private ground_pairing_symmetric from
  D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry

local notation "DΛ" => leechData
private abbrev leechUnit : IsUnit leechData.G.det := leech_spec.2.1
local notation "uΛ" => leechUnit
local notation "V" => ActualGround DΛ uΛ
local notation "T" => ActualTensor DΛ uΛ
local notation "M₀" => paritySpace DΛ uΛ (-1)
local notation "ρ" => groundRepresentation DΛ uΛ
private abbrev groundForm := (selectedGroundPairing DΛ uΛ).form
local notation "B" => groundForm
local notation "H" => chargeForm DΛ ρ

private def groundSquare : ℝ := Classical.choose leechGroundConjugation

/-- The witness supplied by the existing equivariant ground conjugation theorem. -/
def groundConjugation : V →ₗ⋆[ℂ] V :=
  Classical.choose (Classical.choose_spec leechGroundConjugation)

theorem groundConjugation_involutive : Function.Involutive groundConjugation :=
  (Classical.choose_spec (Classical.choose_spec leechGroundConjugation)).2.2.1

theorem groundConjugation_equivariant (g : Extension DΛ ⧸ K DΛ) (x : V) :
    groundConjugation (ρ g x) = ρ g (groundConjugation x) :=
  (Classical.choose_spec (Classical.choose_spec leechGroundConjugation)).2.2.2.1 g x

private theorem groundConjugation_pairing (x y : V) :
    B (groundConjugation x) y = (((Real.sqrt groundSquare)⁻¹ : ℝ) : ℂ) * H x y :=
  (Classical.choose_spec (Classical.choose_spec leechGroundConjugation)).2.2.2.2.1 x y

private theorem groundForm_conjugation (x y : V) :
    B (groundConjugation x) (groundConjugation y) = conj (B x y) := by
  have symmetric := ground_pairing_symmetric DΛ uΛ (selectedGroundPairing DΛ uΛ)
  calc
    B (groundConjugation x) (groundConjugation y) =
        (((Real.sqrt groundSquare)⁻¹ : ℝ) : ℂ) * H x (groundConjugation y) :=
      groundConjugation_pairing _ _
    _ = conj (B (groundConjugation (groundConjugation y)) x) := by
      rw [groundConjugation_pairing, map_mul, Complex.conj_ofReal, charge_form_hermitian]
    _ = conj (B x y) := by
      rw [groundConjugation_involutive y, symmetric.eq y x]

private abbrev oscillatorConjugationRing (D : LatticeData) :
    Oscillator D →+* Oscillator D :=
  MvPolynomial.map (starRingEnd ℂ)

private def oscillatorConjugation (D : LatticeData) : Oscillator D →ₗ⋆[ℂ] Oscillator D where
  toFun := kappaOsc (D := D)
  map_add' := kappaOsc_add (D := D)
  map_smul' := kappaOsc_smul (D := D)

private theorem kappaOsc_sum (D : LatticeData) {ι : Type*} (s : Finset ι)
    (f : ι → Oscillator D) :
    kappaOsc (∑ i ∈ s, f i) = ∑ i ∈ s, kappaOsc (f i) :=
  map_sum (oscillatorConjugationRing D) f s

private theorem modeMatrix_conj (D : LatticeData) (k : ℕ) (i j : Fin D.rank) :
    conj (modeMatrix D k i j) = modeMatrix D k i j := by
  change conj (-LatticeHalfFock.frequency (k : ℤ) * (D.G i j : ℂ)) =
    -LatticeHalfFock.frequency (k : ℤ) * (D.G i j : ℂ)
  simp only [LatticeHalfFock.frequency, map_mul, map_neg, map_add, map_intCast, map_div₀,
    map_one, map_ofNat]

private theorem kappaOsc_variableImage (D : LatticeData) (x : Index D) :
    kappaOsc (OriginalCurrentMetric.variableImage (modeMatrix D) x) =
      OriginalCurrentMetric.variableImage (modeMatrix D) x := by
  classical
  rw [OriginalCurrentMetric.variableImage, kappaOsc_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [kappaOsc_smul, kappaOsc_X, modeMatrix_conj]

private theorem kappaOsc_substitution (D : LatticeData) (p : Oscillator D) :
    kappaOsc (OriginalCurrentMetric.substitution (modeMatrix D) p) =
      OriginalCurrentMetric.substitution (modeMatrix D) (kappaOsc p) := by
  have substitution_C (c : ℂ) :
      OriginalCurrentMetric.substitution (modeMatrix D) (MvPolynomial.C c) =
        MvPolynomial.C c :=
    (OriginalCurrentMetric.substitution (modeMatrix D)).commutes c
  induction p using MvPolynomial.induction_on with
  | C c => simp only [substitution_C, kappaOsc_C]
  | add p q hp hq => simp only [map_add, kappaOsc_add, hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, OriginalCurrentMetric.substitution_X, kappaOsc_mul, kappaOsc_X,
      kappaOsc_variableImage, hp]

private theorem factorialBilinear_kappa (D : LatticeData) (p q : Oscillator D) :
    FactorialBilinear.form (Index D) (kappaOsc p) (kappaOsc q) =
      conj (FactorialBilinear.form (Index D) p q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have monomial_conj :
        kappaOsc (MvPolynomial.monomial d c : Oscillator D) =
          MvPolynomial.monomial d (conj c) :=
      MvPolynomial.map_monomial (starRingEnd ℂ) d c
    simp only [monomial_conj, FactorialBilinear.monomial_left, kappaOsc_coeff, map_mul,
      map_natCast]
  | add p r hp hr =>
    simp only [kappaOsc_add, map_add, LinearMap.add_apply, hp, hr]

/-- The native signed Wick pairing is real for raw polynomial coefficient conjugation. -/
theorem wick_conjugation (D : LatticeData) (p q : Oscillator D) :
    wick D (kappaOsc p) (kappaOsc q) = conj (wick D p q) := by
  change FactorialBilinear.form (Index D)
      (OriginalCurrentMetric.substitution (modeMatrix D) (kappaOsc p)) (kappaOsc q) =
    conj (FactorialBilinear.form (Index D)
      (OriginalCurrentMetric.substitution (modeMatrix D) p) q)
  rw [← kappaOsc_substitution]
  exact factorialBilinear_kappa D _ _

/-- Tensor the two maps over the same scalar conjugation. -/
def tensorConjugation : T →ₗ⋆[ℂ] T :=
  TensorProduct.map (oscillatorConjugation DΛ) groundConjugation

@[simp] theorem tensorConjugation_tmul (p : Oscillator DΛ) (x : V) :
    tensorConjugation (p ⊗ₜ[ℂ] x) = kappaOsc p ⊗ₜ[ℂ] groundConjugation x :=
  TensorProduct.map_tmul _ _ p x

theorem tensorConjugation_involutive : Function.Involutive tensorConjugation := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul p v =>
    rw [tensorConjugation_tmul, tensorConjugation_tmul,
      kappaOsc_involutive, groundConjugation_involutive v]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorConjugation_actualParity (x : T) :
    tensorConjugation (actualParity DΛ uΛ x) = actualParity DΛ uΛ (tensorConjugation x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p v =>
    simp only [actualParity, TensorProduct.map_tmul, LinearMap.id_apply,
      tensorConjugation_tmul]
    change kappaOsc (sigma DΛ p) ⊗ₜ[ℂ] groundConjugation v =
      sigma DΛ (kappaOsc p) ⊗ₜ[ℂ] groundConjugation v
    rw [kappaOsc_sigma]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorConjugation_mem_negative (x : T) (hx : x ∈ M₀) :
    tensorConjugation x ∈ M₀ := by
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  rw [← tensorConjugation_actualParity, hx, map_smulₛₗ, map_neg, map_one]

/-- Restrict to the negative eigenspace used by the actual twisted orbifold sector. -/
def negativeConjugation : M₀ →ₗ⋆[ℂ] M₀ :=
  tensorConjugation.restrict tensorConjugation_mem_negative

theorem negativeConjugation_involutive : Function.Involutive negativeConjugation := by
  intro x
  apply Subtype.ext
  simpa only [negativeConjugation, LinearMap.coe_restrict_apply] using
    tensorConjugation_involutive (x : T)

theorem actualForm_conjugation (x y : T) :
    actualForm DΛ uΛ (tensorConjugation x) (tensorConjugation y) =
      conj (actualForm DΛ uΛ x y) := by
  induction x using TensorProduct.inductionOn generalizing y with
  | tmul p u =>
    induction y using TensorProduct.inductionOn with
    | tmul q v =>
      simp only [tensorConjugation_tmul, actualForm_tmul, groundForm_conjugation,
        wick_conjugation, map_mul]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

theorem actualForm_negativeConjugation (x y : M₀) :
    actualForm DΛ uΛ (negativeConjugation x : T) (negativeConjugation y : T) =
      conj (actualForm DΛ uΛ (x : T) (y : T)) := by
  simpa only [negativeConjugation, LinearMap.coe_restrict_apply] using
    actualForm_conjugation (x : T) (y : T)

private theorem halfCreationSeries_map (D : LatticeData) (a : Charge D) :
    PowerSeries.map (oscillatorConjugationRing D) (halfCreationSeries D a) =
      halfCreationSeries D a := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, halfCreationSeries, PowerSeries.coeff_mk]
  split_ifs
  · change kappaOsc ((2 / (n : ℂ)) •
        ∑ i : Fin D.rank, (a i : ℂ) • (MvPolynomial.X (i, n / 2) : Oscillator D)) = _
    simp only [kappaOsc_smul, map_div₀, map_ofNat, map_natCast,
      kappaOsc_sum, map_intCast, kappaOsc_X]
  · exact map_zero _

private theorem halfCreationCoeff_kappa (D : LatticeData) (a : Charge D) (e : ℤ) :
    kappaOsc (halfCreationCoeff D a e) = halfCreationCoeff D a e := by
  have h : PowerSeries.HasSubst (halfCreationSeries D a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simp [halfCreationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have mapped := PowerSeries.map_subst (h := oscillatorConjugationRing D) h
    (PowerSeries.exp (Oscillator D))
  change PowerSeries.map (oscillatorConjugationRing D) (halfCreationExponential D a) =
    (PowerSeries.map (oscillatorConjugationRing D) (PowerSeries.exp (Oscillator D))).subst
      (PowerSeries.map (oscillatorConjugationRing D) (halfCreationSeries D a)) at mapped
  rw [PowerSeries.map_exp, halfCreationSeries_map] at mapped
  change PowerSeries.map (oscillatorConjugationRing D) (halfCreationExponential D a) =
    halfCreationExponential D a at mapped
  unfold halfCreationCoeff
  split_ifs
  · exact map_zero (oscillatorConjugationRing D)
  · change oscillatorConjugationRing D
      (PowerSeries.coeff e.toNat (halfCreationExponential D a)) = _
    rw [← PowerSeries.coeff_map, mapped]

private theorem halfTranslationVariable_map (D : LatticeData) (a : Charge D) (x : Index D) :
    Polynomial.map (oscillatorConjugationRing D) (halfTranslationVariable D a x) =
      halfTranslationVariable D a x := by
  have variable_fixed : oscillatorConjugationRing D (MvPolynomial.X x) = MvPolynomial.X x :=
    kappaOsc_X (D := D) x
  have constant_fixed :
      oscillatorConjugationRing D
        ((bilinear D a (unitCharge D x.1) : ℂ) • (1 : Oscillator D)) =
        (bilinear D a (unitCharge D x.1) : ℂ) • (1 : Oscillator D) := by
    change kappaOsc ((bilinear D a (unitCharge D x.1) : ℂ) • (1 : Oscillator D)) = _
    rw [kappaOsc_smul, map_intCast]
    change _ • oscillatorConjugationRing D (1 : Oscillator D) = _
    rw [map_one]
  simp only [halfTranslationVariable, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, variable_fixed, constant_fixed]

private theorem halfTranslatedPolynomial_map (D : LatticeData) (a : Charge D) (p : Oscillator D) :
    Polynomial.map (oscillatorConjugationRing D) (halfTranslatedPolynomial D a p) =
      halfTranslatedPolynomial D a (kappaOsc p) := by
  have translated_C (c : ℂ) :
      halfTranslatedPolynomial D a (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) :=
    (MvPolynomial.aeval (halfTranslationVariable D a)).commutes c
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [translated_C, kappaOsc_C, Polynomial.map_C]
    exact congrArg (Polynomial.C : Oscillator D → Polynomial (Oscillator D))
      (kappaOsc_C (D := D) c)
  | add p q hp hq =>
    simp only [kappaOsc_add, halfTranslatedPolynomial, map_add, Polynomial.map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p x hp =>
    let translate : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) :=
      MvPolynomial.aeval (halfTranslationVariable D a)
    change Polynomial.map (oscillatorConjugationRing D) (translate (p * MvPolynomial.X x)) =
      translate (kappaOsc (p * MvPolynomial.X x))
    have hx : translate (MvPolynomial.X x) = halfTranslationVariable D a x :=
      MvPolynomial.aeval_X _ _
    simp only [kappaOsc_mul, kappaOsc_X, map_mul, hx, Polynomial.map_mul,
      halfTranslationVariable_map]
    rw [show Polynomial.map (oscillatorConjugationRing D) (translate p) =
      translate (kappaOsc p) from hp]

private theorem kappaOsc_oscillatorCoefficient (D : LatticeData) (a : Charge D) (e : ℤ)
    (p : Oscillator D) :
    kappaOsc (oscillatorCoefficient D a e p) = oscillatorCoefficient D a e (kappaOsc p) := by
  change oscillatorConjugationRing D (∑ᶠ n : ℕ, oscillatorTerm D a e p n) =
    ∑ᶠ n : ℕ, oscillatorTerm D a e (kappaOsc p) n
  rw [map_finsum _ (charged_term_finite_support D a e p)]
  apply finsum_congr
  intro n
  change kappaOsc (oscillatorTerm D a e p n) = _
  have coeff_conj :
      kappaOsc ((halfTranslatedPolynomial D a p).coeff n) =
        (halfTranslatedPolynomial D a (kappaOsc p)).coeff n := by
    change oscillatorConjugationRing D ((halfTranslatedPolynomial D a p).coeff n) = _
    rw [← Polynomial.coeff_map, halfTranslatedPolynomial_map]
  simp only [oscillatorTerm, kappaOsc_mul, coeff_conj, halfCreationCoeff_kappa]

private theorem chargeScalar_conj (a : Charge DΛ) :
    conj (chargeScalar DΛ a) = chargeScalar DΛ a := by
  simp only [chargeScalar, map_zpow₀, map_ofNat]

/-- Commutation with the literal charged tensor coefficient on the full twisted state space. -/
theorem tensorConjugation_chargedCoefficient (a : Charge DΛ) (e : ℤ) (x : T) :
    tensorConjugation (chargedCoefficient DΛ uΛ a e x) =
      chargedCoefficient DΛ uΛ a e (tensorConjugation x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p v =>
    simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
      map_smulₛₗ, tensorConjugation_tmul, chargeScalar_conj, kappaOsc_oscillatorCoefficient,
      groundAction, groundConjugation_equivariant]
  | add x y hx hy => simp only [map_add, hx, hy]

end D5.S3.VertexAlgebra.TwistedGround.ActualLeechTwistedTensorRealForm
