/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeNormalActions
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeNormalActions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite native normal-word actions with full repeated-current Leibniz contractions. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
import D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeActualAnnihilation MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

abbrev PolynomialDerivation (D : LatticeData) :=
  Derivation ℂ (Oscillator D) (Oscillator D)

def derivativeWord (D : LatticeData) :
    List (PolynomialDerivation D) → Module.End ℂ (Oscillator D)
  | [] => 1
  | derivative :: remaining => derivativeWord D remaining * derivative.toLinearMap

def derivativeSplits (D : LatticeData) : List (PolynomialDerivation D) →
    List (List (PolynomialDerivation D) × List (PolynomialDerivation D))
  | [] => [([], [])]
  | derivative :: remaining =>
    (derivativeSplits D remaining).map (fun split => (derivative :: split.1, split.2)) ++
      (derivativeSplits D remaining).map (fun split => (split.1, derivative :: split.2))

private theorem derivativeWord_mul (D : LatticeData)
    (derivatives : List (PolynomialDerivation D)) (first second : Oscillator D) :
    derivativeWord D derivatives (first * second) =
      ((derivativeSplits D derivatives).map (fun split =>
        derivativeWord D split.1 first * derivativeWord D split.2 second)).sum := by
  induction derivatives generalizing first second with
  | nil => simp [derivativeWord, derivativeSplits]
  | cons derivative remaining inductionProof =>
    simp only [derivativeWord, Module.End.mul_apply, Derivation.coeFn_coe]
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add]
    rw [mul_comm second (derivative first), inductionProof, inductionProof]
    simp only [derivativeSplits, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, derivativeWord, Module.End.mul_apply, Derivation.coeFn_coe]
    rw [add_comm]

def positiveDerivatives (D : LatticeData) :
    (word : List (Index D)) → ModeTuple D word → List (PolynomialDerivation D)
  | [], _ => []
  | index :: remaining, modes =>
    if modes.1 < 0 then positiveDerivatives D remaining modes.2
    else ((jetScalar index.2 modes.1 * LatticeHalfFock.frequency modes.1) •
      annihilationDerivation D index.1 modes.1.toNat) ::
        positiveDerivatives D remaining modes.2

def creationFactor (D : LatticeData) :
    (word : List (Index D)) → ModeTuple D word → Oscillator D
  | [], _ => 1
  | index :: remaining, modes =>
    if modes.1 < 0 then jetScalar index.2 modes.1 •
      (X (index.1, (-modes.1 - 1).toNat) * creationFactor D remaining modes.2)
    else creationFactor D remaining modes.2

def tensorMultiply (D : LatticeData) (hu : IsUnit D.G.det) (polynomial : Oscillator D) :
    Module.End ℂ (ActualTensor D hu) :=
  LatticeHalfFock.tensorEnd D (ActualGround D hu) (LinearMap.mulLeft ℂ polynomial)

private theorem rightAction_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (modes : ModeTuple D word)
    (polynomial : Oscillator D) (ground : ActualGround D hu) :
    rightAction D hu word modes (polynomial ⊗ₜ[ℂ] ground) =
      derivativeWord D (positiveDerivatives D word modes) polynomial ⊗ₜ[ℂ] ground := by
  induction word generalizing polynomial with
  | nil => simp [rightAction, positiveDerivatives, derivativeWord]
  | cons index remaining inductionProof =>
    simp only [rightAction, positiveDerivatives]
    split_ifs with negative
    · exact inductionProof modes.2 polynomial
    · simp only [Module.End.mul_apply, jetCurrent, LinearMap.smul_apply,
        LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
        TensorProduct.map_tmul, LinearMap.id_apply, LatticeHalfFock.current,
        if_neg negative, TensorProduct.smul_tmul', ← smul_smul]
      rw [inductionProof]
      simp [derivativeWord, Derivation.coeFn_coe, annihilation_apply, smul_smul]

private theorem leftAction_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (modes : ModeTuple D word)
    (polynomial : Oscillator D) (ground : ActualGround D hu) :
    leftAction D hu word modes (polynomial ⊗ₜ[ℂ] ground) =
      (creationFactor D word modes * polynomial) ⊗ₜ[ℂ] ground := by
  induction word generalizing polynomial with
  | nil => simp [leftAction, creationFactor]
  | cons index remaining inductionProof =>
    simp only [leftAction, creationFactor]
    split_ifs with negative
    · simp only [Module.End.mul_apply, inductionProof, jetCurrent, LinearMap.smul_apply,
        LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
        TensorProduct.map_tmul, LinearMap.id_apply, LatticeHalfFock.current,
        if_pos negative, LinearMap.mulLeft_apply, TensorProduct.smul_tmul', smul_mul_assoc,
        mul_assoc]
    · exact inductionProof modes.2 polynomial

def rightSplitAction (D : LatticeData) (hu : IsUnit D.G.det)
    (polynomial : Oscillator D) (split : List (PolynomialDerivation D) ×
      List (PolynomialDerivation D)) : Module.End ℂ (ActualTensor D hu) :=
  tensorMultiply D hu (derivativeWord D split.1 polynomial) *
    LatticeHalfFock.tensorEnd D (ActualGround D hu) (derivativeWord D split.2)

private theorem end_sum_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (operators : List (Module.End ℂ (ActualTensor D hu))) (state : ActualTensor D hu) :
    operators.sum state = (operators.map (fun operator => operator state)).sum := by
  induction operators with
  | nil => simp
  | cons operator remaining inductionProof => simp [inductionProof]

theorem actual_positive_word_leibniz (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (modes : ModeTuple D word) (polynomial : Oscillator D)
    (state : ActualTensor D hu) :
    rightAction D hu word modes (tensorMultiply D hu polynomial state) =
      ((derivativeSplits D (positiveDerivatives D word modes)).map
        (rightSplitAction D hu polynomial)).sum state := by
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul target ground =>
    simp only [tensorMultiply, LatticeHalfFock.tensorEnd, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.mulLeft_apply, rightAction_tmul]
    rw [derivativeWord_mul]
    simp only [end_sum_apply, List.map_map, Function.comp_def, rightSplitAction,
      Module.End.mul_apply, tensorMultiply, LatticeHalfFock.tensorEnd,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    induction derivativeSplits D (positiveDerivatives D word modes) with
    | nil => simp
    | cons split remaining inductionProof =>
      simp [inductionProof, TensorProduct.add_tmul, rightSplitAction, tensorMultiply,
        LatticeHalfFock.tensorEnd, Module.End.mul_apply]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]

def normalSplitAction (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (modes : ModeTuple D word)
    (exponent : ℤ) (polynomial : Oscillator D)
    (split : List (PolynomialDerivation D) × List (PolynomialDerivation D)) :
    Module.End ℂ (ActualTensor D hu) :=
  chargeScalar D charge • TensorProduct.map
    (LinearMap.mulLeft ℂ (creationFactor D word modes) *
      oscillatorCoefficient D charge (exponent + 2 * modeSum D word modes + jetShift D word) *
        LinearMap.mulLeft ℂ (derivativeWord D split.1 polynomial) * derivativeWord D split.2)
    (groundAction D hu charge)

def normalSplitCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (exponent : ℤ)
    (polynomial : Oscillator D) (modes : ModeTuple D word) :
    Module.End ℂ (ActualTensor D hu) :=
  ((derivativeSplits D (positiveDerivatives D word modes)).map
    (normalSplitAction D hu charge word modes exponent polynomial)).sum

private theorem flatCoefficient_split (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (modes : ModeTuple D word)
    (exponent : ℤ) (polynomial : Oscillator D) (state : ActualTensor D hu) :
    flatTerm D hu (chargedField D hu charge) word exponent
        (tensorMultiply D hu polynomial state) modes =
      normalSplitCoefficient D hu charge word exponent polynomial modes state := by
  simp only [flatTerm, flatCoefficient_factorization, Module.End.mul_apply]
  rw [actual_positive_word_leibniz]
  rw [end_sum_apply]
  rw [map_list_sum, map_list_sum]
  simp only [normalSplitCoefficient, end_sum_apply, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro split member
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul target ground =>
    simp only [rightSplitAction, normalSplitAction, Module.End.mul_apply, tensorMultiply,
      LatticeHalfFock.tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.mulLeft_apply, chargedField, HVertexOperator.coeff_of_coeff,
      chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
      map_smul, leftAction_tmul]
  | add first second firstProof secondProof => simp only [map_add, firstProof, secondProof]

theorem actual_normal_word_finite_action (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (exponent : ℤ)
    (polynomial : Oscillator D) (state : ActualTensor D hu) :
    ∃ finiteModes : Finset (ModeTuple D word),
      (∀ modes ∉ finiteModes,
        normalSplitCoefficient D hu charge word exponent polynomial modes state = 0) ∧
      (normalWord D hu charge word).coeff exponent (tensorMultiply D hu polynomial state) =
        ∑ modes ∈ finiteModes,
          normalSplitCoefficient D hu charge word exponent polynomial modes state := by
  classical
  have finite := flatTerm_finite D hu (chargedField D hu charge) word exponent
    (tensorMultiply D hu polynomial state)
  refine ⟨finite.toFinset, ?_, ?_⟩
  · intro modes outside
    rw [← flatCoefficient_split]
    have absent : modes ∉ Function.support
        (flatTerm D hu (chargedField D hu charge) word exponent
          (tensorMultiply D hu polynomial state)) := by
      simpa only [Set.Finite.mem_toFinset] using outside
    change ¬ flatTerm D hu (chargedField D hu charge) word exponent
      (tensorMultiply D hu polynomial state) modes ≠ 0 at absent
    exact not_not.mp absent
  · rw [normalWord_flattened,
      finsum_eq_sum_of_support_subset _ (show Function.support
        (flatTerm D hu (chargedField D hu charge) word exponent
          (tensorMultiply D hu polynomial state)) ⊆ (finite.toFinset : Set _) by
        rw [Set.Finite.coe_toFinset])]
    apply Finset.sum_congr rfl
    intro modes member
    exact flatCoefficient_split D hu charge word modes exponent polynomial state

private theorem normalPolynomial_finite_action (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (source : Oscillator D) (exponent : ℤ)
    (polynomial : Oscillator D) (state : ActualTensor D hu) :
    ∃ finiteModes : (monomial : Index D →₀ ℕ) →
        Finset (ModeTuple D (LatticeAllStateField.occurrences D monomial)),
      (∀ monomial ∈ source.support, ∀ modes ∉ finiteModes monomial,
        normalSplitCoefficient D hu charge (LatticeAllStateField.occurrences D monomial)
          exponent polynomial modes state = 0) ∧
      (normalPolynomial D hu charge source).coeff exponent (tensorMultiply D hu polynomial state) =
        ∑ monomial ∈ source.support, MvPolynomial.coeff monomial source •
          ∑ modes ∈ finiteModes monomial,
            normalSplitCoefficient D hu charge (LatticeAllStateField.occurrences D monomial)
              exponent polynomial modes state := by
  classical
  choose finiteModes missing action using (fun monomial : Index D →₀ ℕ =>
    actual_normal_word_finite_action D hu charge (LatticeAllStateField.occurrences D monomial)
      exponent polynomial state)
  refine ⟨finiteModes, fun monomial _ => missing monomial, ?_⟩
  rw [normalPolynomial_enumerated_expansion D hu charge source
    (LatticeAllStateField.occurrences D) (fun monomial _ => List.Perm.refl _)]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro monomial member
  rw [action monomial]

def correctionCoefficients (D : LatticeData)
    (source : LatticeHalfFockFiniteCorrection.CorrectionPolynomial D) : ℕ →₀ Oscillator D :=
  LatticeHalfFockFiniteCorrection.shiftCoefficients D (optionEquivLeft ℂ (Index D) source)

theorem actual_native_correction_finite_action (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (source : LatticeHalfFockFiniteCorrection.CorrectionPolynomial D)
    (exponent : ℤ) (polynomial : Oscillator D) (state : ActualTensor D hu) :
    ∃ finiteModes : (shift : ℕ) → (monomial : Index D →₀ ℕ) →
        Finset (ModeTuple D (LatticeAllStateField.occurrences D monomial)),
      (∀ shift ∈ (correctionCoefficients D source).support,
        ∀ monomial ∈ (correctionCoefficients D source shift).support,
          ∀ modes ∉ finiteModes shift monomial,
            normalSplitCoefficient D hu charge (LatticeAllStateField.occurrences D monomial)
              (exponent + 2 * shift) polynomial modes state = 0) ∧
      (LatticeHalfFockScalarLabelledGaussian.nativeCorrectionEvaluation D hu charge source).coeff
          exponent (tensorMultiply D hu polynomial state) =
        ∑ shift ∈ (correctionCoefficients D source).support,
          ∑ monomial ∈ (correctionCoefficients D source shift).support,
            MvPolynomial.coeff monomial (correctionCoefficients D source shift) •
              ∑ modes ∈ finiteModes shift monomial,
                normalSplitCoefficient D hu charge (LatticeAllStateField.occurrences D monomial)
                  (exponent + 2 * shift) polynomial modes state := by
  classical
  choose finiteModes missing action using (fun shift : ℕ =>
    normalPolynomial_finite_action D hu charge (correctionCoefficients D source shift)
      (exponent + 2 * shift) polynomial state)
  refine ⟨finiteModes, fun shift _ => missing shift, ?_⟩
  change (Finsupp.lsum ℂ (fun shift : ℕ =>
    (shiftLinear D hu shift).comp (normalPolynomial D hu charge))
      (correctionCoefficients D source)).coeff exponent
        (tensorMultiply D hu polynomial state) = _
  rw [Finsupp.lsum_apply]
  simp only [Finsupp.sum, map_sum, Finset.sum_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, shiftLinear, shiftField, LinearMap.coe_mk, AddHom.coe_mk,
    HVertexOperator.coeff_of_coeff]
  apply Finset.sum_congr rfl
  intro shift member
  exact action shift

#print axioms actual_positive_word_leibniz
#print axioms actual_normal_word_finite_action
#print axioms actual_native_correction_finite_action

end

end D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions
