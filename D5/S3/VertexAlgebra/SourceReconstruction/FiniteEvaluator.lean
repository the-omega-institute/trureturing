/- GID: D5/S3/VertexAlgebra/SourceReconstruction/FiniteEvaluator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceReconstruction/FiniteEvaluator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Natural-weight finite reconstruction of every original native twisted field coefficient. -/

import D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.SourceReconstruction.FiniteEvaluator

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeHalfFockFirstDescendant LatticeHalfFockOriginalMixedIterate
open LatticeHalfFockAllStateField LatticeHalfFockAllStateCurrentCommutator
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFiniteCorrection LatticeHalfFockCurrentBorcherds
open OscillatorWords OscillatorWeight NativeDescendants MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

def targetCutoff (D : LatticeData) (hu : IsUnit D.G.det) (vector : ActualTensor D hu) : ℕ :=
  Classical.choose (LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector)

def nativeCutoff (D : LatticeData) (hu : IsUnit D.G.det) (degree : ℕ)
    (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) : ℕ :=
  max ((exponent + 1 - coefficientOrderMinimum D hu source vector +
      2 * (sourceWeightBound D source : ℤ)).toNat + 1)
    (max (targetCutoff D hu vector + 1) (vectorFrequencyBound D source + degree + 1))

theorem native_terms_vanish (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) (outside : nativeCutoff D hu degree source exponent vector ≤ offset) :
    nativeFirst D hu colour degree source exponent vector offset = 0 ∧
      nativeSecond D hu colour degree source exponent vector offset = 0 ∧
      nativeCorrection D hu colour degree source exponent vector offset = 0 := by
  unfold nativeCutoff at outside
  have first : (exponent + 1 - coefficientOrderMinimum D hu source vector +
      2 * (sourceWeightBound D source : ℤ)).toNat + 1 ≤ offset := by omega
  have second : targetCutoff D hu vector ≤ offset := by omega
  have third : vectorFrequencyBound D source + degree + 1 ≤ offset := by omega
  constructor
  · unfold nativeFirst
    rw [Ytw_source_lower_truncation D hu source vector _ (by omega), map_zero]
  constructor
  · have truncation := Classical.choose_spec
      (LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector)
    have zero : currentCombination D hu (Pi.single colour 1) (offset : ℤ) vector = 0 := by
      simp only [currentCombination, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_eq_zero
      intro other member
      rw [truncation other offset (by exact_mod_cast second), smul_zero]
    simp [nativeSecond, zero]
  · have zero : ((unitCurrent D colour)[[-(degree : ℤ) + offset]]) source = 0 :=
      sourceCurrent_upper_truncation D (Pi.single colour 1) source _ (by omega)
    simp [nativeCorrection, zero]

theorem native_descendant_finite (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    (Ytw D hu (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) source)).coeff exponent vector =
      (∑ offset ∈ Finset.range (nativeCutoff D hu degree source exponent vector),
        ((degree + offset).choose degree : ℂ) •
          (nativeFirst D hu colour degree source exponent vector offset +
            (-1 : ℂ) ^ degree • nativeSecond D hu colour degree source exponent vector offset)) -
      ∑ offset ∈ Finset.range (nativeCutoff D hu degree source exponent vector),
        Ring.choose (1 / 2 : ℂ) (offset + 1) •
          nativeCorrection D hu colour degree source exponent vector offset := by
  have secondFinite : Function.HasFiniteSupport (fun offset : ℕ => (-1 : ℂ) ^ degree •
      nativeSecond D hu colour degree source exponent vector offset) :=
    Function.HasFiniteSupport.smul_right (fun _ : ℕ => (-1 : ℂ) ^ degree)
      (nativeSecond_finite D hu colour degree source exponent vector)
  have firstFinite : Function.HasFiniteSupport (fun offset : ℕ =>
      ((degree + offset).choose degree : ℂ) •
        (nativeFirst D hu colour degree source exponent vector offset +
          (-1 : ℂ) ^ degree • nativeSecond D hu colour degree source exponent vector offset)) :=
    Function.HasFiniteSupport.smul_right (fun offset : ℕ => ((degree + offset).choose degree : ℂ))
      ((nativeFirst_finite D hu colour degree source exponent vector).add secondFinite)
  have correctionFinite : Function.HasFiniteSupport (fun offset : ℕ =>
      Ring.choose (1 / 2 : ℂ) (offset + 1) •
        nativeCorrection D hu colour degree source exponent vector offset) :=
    Function.HasFiniteSupport.smul_right (fun offset : ℕ => Ring.choose (1 / 2 : ℂ) (offset + 1))
      (nativeCorrection_finite D hu colour degree source exponent vector)
  rw [native_descendant]
  congr 1
  · apply finsum_eq_sum_of_support_toFinset_subset _ firstFinite
    intro offset member
    have nonzero := firstFinite.mem_toFinset.mp member
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra outside
    obtain ⟨first, second, third⟩ := native_terms_vanish D hu colour degree source exponent vector
      offset (by omega)
    exact nonzero (by simp [first, second])
  · apply finsum_eq_sum_of_support_toFinset_subset _ correctionFinite
    intro offset member
    have nonzero := correctionFinite.mem_toFinset.mp member
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra outside
    have third := (native_terms_vanish D hu colour degree source exponent vector offset (by omega)).2.2
    exact nonzero (by simp [third])

abbrev Evaluator (D : LatticeData) (hu : IsUnit D.G.det) :=
  Carrier D → ℤ → ActualTensor D hu → ActualTensor D hu

def wordStep (D : LatticeData) (hu : IsUnit D.G.det) (evaluate : Evaluator D hu)
    (charge : Charge D) : List (Index D) → ℤ → ActualTensor D hu → ActualTensor D hu
  | [], exponent, vector => (chargedField D hu charge).coeff exponent vector
  | index :: tail, exponent, vector =>
    let source := oscillatorWord D charge tail
    let cutoff := nativeCutoff D hu index.2 source exponent vector
    (∑ offset ∈ Finset.range cutoff, ((index.2 + offset).choose index.2 : ℂ) •
      (currentCombination D hu (Pi.single index.1 1) (-(index.2 : ℤ) - 1 - offset)
        (evaluate source (exponent + 1 - 2 * offset) vector) +
        (-1 : ℂ) ^ index.2 • evaluate source (exponent + 2 * index.2 + 3 + 2 * offset)
          (currentCombination D hu (Pi.single index.1 1) offset vector))) -
      ∑ offset ∈ Finset.range cutoff, Ring.choose (1 / 2 : ℂ) (offset + 1) •
        evaluate (((unitCurrent D index.1)[[-(index.2 : ℤ) + offset]]) source)
          (exponent + 2 * offset + 2) vector

def expandState (D : LatticeData) (hu : IsUnit D.G.det)
    (evaluateWord : Charge D → List (Index D) → ℤ → ActualTensor D hu → ActualTensor D hu)
    (state : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) : ActualTensor D hu :=
  ∑ charge ∈ state.support,
    ∑ monomial ∈ ((basisMonomials (Index D) ℂ).repr (state charge)).support,
      ((basisMonomials (Index D) ℂ).repr (state charge) monomial) •
        evaluateWord charge (LatticeAllStateField.occurrences D monomial) exponent vector

def evaluateFuel (D : LatticeData) (hu : IsUnit D.G.det) : ℕ → Evaluator D hu
  | 0 => expandState D hu (fun charge _ exponent vector =>
      (chargedField D hu charge).coeff exponent vector)
  | fuel + 1 => expandState D hu (wordStep D hu (evaluateFuel D hu fuel))

def evaluate (D : LatticeData) (hu : IsUnit D.G.det) (state : Carrier D) :
    ℤ → ActualTensor D hu → ActualTensor D hu :=
  evaluateFuel D hu (sourceWeightBound D state) state

theorem wordStep_agrees (D : LatticeData) (hu : IsUnit D.G.det) (evaluate : Evaluator D hu)
    (charge : Charge D) (word : List (Index D))
    (agrees : ∀ source : Carrier D, sourceWeightBound D source < wordWeight D word →
      ∀ exponent vector, evaluate source exponent vector = (Ytw D hu source).coeff exponent vector)
    (exponent : ℤ) (vector : ActualTensor D hu) :
    wordStep D hu evaluate charge word exponent vector =
      (Ytw D hu (oscillatorWord D charge word)).coeff exponent vector := by
  cases word with
  | nil => simp [wordStep, oscillatorWord, Ytw_charge]
  | cons index tail =>
    have tailBound := oscillatorWord_weight_le D charge tail
    have tailLower : sourceWeightBound D (oscillatorWord D charge tail) <
        wordWeight D (index :: tail) := by
      simp only [wordWeight, List.map_cons, List.sum_cons, sourceWeight] at *
      omega
    have correctionLower (offset : ℕ) :
        sourceWeightBound D (((unitCurrent D index.1)[[-(index.2 : ℤ) + offset]])
          (oscillatorWord D charge tail)) < wordWeight D (index :: tail) := by
      have lower := correction_source_weight_lt D index.1 index.2 offset (oscillatorWord D charge tail)
      simp only [wordWeight, List.map_cons, List.sum_cons, sourceWeight] at *
      omega
    simp only [wordStep, oscillatorWord, native_descendant_finite]
    simp only [agrees _ tailLower, agrees _ (correctionLower _),
      nativeFirst, nativeSecond, nativeCorrection]

private def nativeEvaluation (D : LatticeData) (hu : IsUnit D.G.det)
    (exponent : ℤ) (vector : ActualTensor D hu) : Carrier D →ₗ[ℂ] ActualTensor D hu where
  toFun source := (Ytw D hu source).coeff exponent vector
  map_add' first second := by simp
  map_smul' scalar source := by simp

theorem expandState_agrees (D : LatticeData) (hu : IsUnit D.G.det)
    (evaluateWord : Charge D → List (Index D) → ℤ → ActualTensor D hu → ActualTensor D hu)
    (state : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu)
    (agrees : ∀ charge ∈ state.support,
      ∀ monomial ∈ ((basisMonomials (Index D) ℂ).repr (state charge)).support,
        evaluateWord charge (LatticeAllStateField.occurrences D monomial) exponent vector =
          (Ytw D hu (oscillatorWord D charge (LatticeAllStateField.occurrences D monomial))).coeff
            exponent vector) :
    expandState D hu evaluateWord state exponent vector = (Ytw D hu state).coeff exponent vector := by
  have expansion := congrArg (nativeEvaluation D hu exponent vector) (finite_source_expansion D state)
  simp only [map_sum, map_smul] at expansion
  rw [show (Ytw D hu state).coeff exponent vector = _ from expansion]
  unfold expandState
  apply Finset.sum_congr rfl
  intro charge chargeMember
  apply Finset.sum_congr rfl
  intro monomial monomialMember
  rw [agrees charge chargeMember monomial monomialMember]
  rfl

theorem evaluateFuel_agrees (D : LatticeData) (hu : IsUnit D.G.det) (fuel : ℕ)
    (state : Carrier D) (bounded : sourceWeightBound D state ≤ fuel)
    (exponent : ℤ) (vector : ActualTensor D hu) :
    evaluateFuel D hu fuel state exponent vector = (Ytw D hu state).coeff exponent vector := by
  induction fuel generalizing state exponent vector with
  | zero =>
    apply expandState_agrees
    intro charge chargeMember monomial monomialMember
    have weight := occurrence_weight_le D state charge chargeMember monomial monomialMember
    cases identity : LatticeAllStateField.occurrences D monomial with
    | nil => simp [identity, oscillatorWord, Ytw_charge]
    | cons index tail =>
      simp only [identity, wordWeight, List.map_cons, List.sum_cons, sourceWeight] at weight
      omega
  | succ fuel inductionHypothesis =>
    apply expandState_agrees
    intro charge chargeMember monomial monomialMember
    apply wordStep_agrees
    intro smaller smallerBound smallerExponent smallerVector
    have weight := occurrence_weight_le D state charge chargeMember monomial monomialMember
    exact inductionHypothesis smaller (by omega) smallerExponent smallerVector

theorem evaluate_agrees (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    evaluate D hu state exponent vector = (Ytw D hu state).coeff exponent vector :=
  evaluateFuel_agrees D hu (sourceWeightBound D state) state le_rfl exponent vector

end
end D5.S3.VertexAlgebra.SourceReconstruction.FiniteEvaluator
