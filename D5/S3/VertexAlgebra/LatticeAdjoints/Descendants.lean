/- GID: D5/S3/VertexAlgebra/LatticeAdjoints/Descendants
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeAdjoints/Descendants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native opposite coefficients give adjoints of unrestricted lattice descendants. -/

import D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure
import D5.S3.VertexAlgebra.LatticeChargedFockForms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeAdjoints.Descendants

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeSugawaraLocalNilpotence LatticeOppositeCoefficients
open LatticeOppositeCurrentClosure LatticeChargedFockForms MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

attribute [local irreducible] neutralMode Y oppositeCoeff bpzForm hermitianForm pct

private theorem opposite_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (charge : Charge D) (index : ℤ) :
    oppositeCoeff D H (chargeEnergy D charge) (Finsupp.single charge (1 : Oscillator D)) index =
      paritySign (chargeEnergy D charge) •
        ((actualField D charge)[[2 * chargeEnergy D charge - index - 2]]) := by
  classical
  have bound : oscillatorBound D (Finsupp.single charge (1 : Oscillator D)) = 0 := by
    rw [show Finsupp.single charge (1 : Oscillator D) = carrierBasis D (charge, 0) by
      simp [carrierBasis_apply] ]
    unfold oscillatorBound
    rw [carrierCoeffEquiv_basis]
    simp [oscillatorEnergy]
  simp only [oppositeCoeff, bound, zero_add, Finset.sum_range_one, oppositeTerm,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply, Int.natCast_zero, sub_zero]
  rw [stateField_ground]

private theorem bpz_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (charge : Charge D)
    (left right : Carrier D) (index : ℤ) :
    bpzForm D (((Y D (Finsupp.single charge (1 : Oscillator D)))[[index]]) left) right =
      bpzForm D left (oppositeCoeff D H (chargeEnergy D charge)
        (Finsupp.single charge (1 : Oscillator D)) index right) := by
  rw [stateField_ground, bpz_charged, opposite_ground, LinearMap.smul_apply, map_smul]
  rw [two_chargeEnergy]
  rfl

private theorem bpz_current_step (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (degree : ℕ) (state : Carrier D) (weight : ℤ)
    (homogeneous : state ∈ grade D weight)
    (inductionHypothesis : ∀ (left right : Carrier D) (index : ℤ),
      bpzForm D (((Y D state)[[index]]) left) right =
        bpzForm D left (oppositeCoeff D H weight state index right))
    (left right : Carrier D) (index : ℤ) :
    bpzForm D (((Y D (neutralMode D current (-(degree : ℤ) - 1) state))[[index]]) left) right =
      bpzForm D left (oppositeCoeff D H (weight + degree + 1)
        (neutralMode D current (-(degree : ℤ) - 1) state) index right) := by
  classical
  have original := current_negative_insertion D current degree state left index
  let first : ℕ → Carrier D := fun offset =>
    ((degree + offset).choose degree : ℂ) •
      neutralMode D current (-(offset : ℤ) - degree - 1)
        (((Y D state)[[index + offset]]) left)
  let second : ℕ → Carrier D := fun offset =>
    ((degree + offset).choose degree : ℂ) •
      ((Y D state)[[index - offset - degree - 1]]) (neutralMode D current offset left)
  have firstTranspose : ∀ offset, bpzForm D (first offset) right =
      -bpzForm D left (reversedFirstTerm D H current degree weight state index right offset) := by
    intro offset
    have mode : -(-(offset : ℤ) - degree - 1) = offset + degree + 1 := by omega
    simp only [first, reversedFirstTerm, map_smul, LinearMap.smul_apply,
      bpz_neutral, mode, inductionHypothesis, smul_eq_mul]
    ring
  have secondTranspose : ∀ offset, bpzForm D (second offset) right =
      -bpzForm D left (reversedSecondTerm D H current degree weight state index right offset) := by
    intro offset
    simp only [second, reversedSecondTerm, map_smul, LinearMap.smul_apply,
      inductionHypothesis, bpz_neutral, smul_eq_mul]
    ring
  have firstSum := ((bpzForm D).flip right).toAddMonoidHom.map_finsum original.1
  have secondSum := ((bpzForm D).flip right).toAddMonoidHom.map_finsum original.2.1
  have reversedFirst := (bpzForm D left).toAddMonoidHom.map_finsum
    (reversed_first_finite D H current degree weight state index right)
  have reversedSecond := (bpzForm D left).toAddMonoidHom.map_finsum
    (reversed_second_finite D H current degree weight state index right)
  change bpzForm D left (∑ᶠ offset,
    reversedFirstTerm D H current degree weight state index right offset) =
      ∑ᶠ offset, bpzForm D left
        (reversedFirstTerm D H current degree weight state index right offset) at reversedFirst
  change bpzForm D left (∑ᶠ offset,
    reversedSecondTerm D H current degree weight state index right offset) =
      ∑ᶠ offset, bpzForm D left
        (reversedSecondTerm D H current degree weight state index right offset) at reversedSecond
  change bpzForm D (∑ᶠ offset, first offset) right =
    ∑ᶠ offset, bpzForm D (first offset) right at firstSum
  change bpzForm D (∑ᶠ offset, second offset) right =
    ∑ᶠ offset, bpzForm D (second offset) right at secondSum
  simp_rw [firstTranspose] at firstSum
  simp_rw [secondTranspose] at secondSum
  rw [finsum_neg_distrib, ← reversedFirst] at firstSum
  rw [finsum_neg_distrib, ← reversedSecond] at secondSum
  rw [original.2.2, opposite_current_insertion D H hHG hGH current degree state right
    weight index homogeneous]
  change bpzForm D ((∑ᶠ offset, first offset) +
    (-1 : ℂ)^degree • ∑ᶠ offset, second offset) right = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    map_neg, firstSum, secondSum, pow_succ]
  module

private theorem basis_grade (D : LatticeData) (label : Label D) :
    carrierBasis D label ∈ grade D (energy D label) := by
  classical
  rw [mem_grade_iff]
  intro other different
  change carrierCoeffEquiv D (carrierBasis D label) other = 0
  rw [carrierCoeffEquiv_basis]
  by_cases same : label = other
  · subst other
    exact (different rfl).elim
  · simp [Finsupp.single_apply, same]

private theorem pct_basis (D : LatticeData) (label : Label D) :
    pct D (carrierBasis D label) =
      ((-1 : ℂ)^(occurrences D label.2).length) • carrierBasis D (-label.1, label.2) := by
  rw [carrierBasis_apply]
  simp only [pct, coefficientConjugation, LinearMap.comp_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  change LatticeInvolution.thetaLinear D
    (Finsupp.single label.1 (LatticeOscillatorFockForm.conjugatePolynomial D (monomial label.2
      1))) = _
  have conjugation : LatticeOscillatorFockForm.conjugatePolynomial D (monomial label.2 1) =
      monomial label.2 1 := by
    change MvPolynomial.map (starRingEnd ℂ) (monomial label.2 1) = _
    simp
  rw [conjugation, LatticeInvolution.theta_single, LatticeInvolution.sigma_monomial,
    carrierBasis_apply, Finsupp.smul_single]

theorem pct_grade (D : LatticeData) (state : Carrier D) (weight : ℤ)
    (homogeneous : state ∈ grade D weight) : pct D state ∈ grade D weight := by
  classical
  rw [grade_eq_span] at homogeneous
  induction homogeneous using Submodule.span_induction with
  | mem vector membership =>
    obtain ⟨label, matching, rfl⟩ := membership
    change energy D label = weight at matching
    rw [pct_basis]
    apply (grade D weight).smul_mem
    have reflected : energy D (-label.1, label.2) = weight := by
      simpa only [energy, chargeEnergy, LatticeInvolution.bilinear_neg_neg] using matching
    rw [← reflected]
    exact basis_grade D (-label.1, label.2)
  | zero => simpa only [map_zero] using (grade D weight).zero_mem
  | add first second _ _ firstInduction secondInduction =>
    simpa only [map_add] using (grade D weight).add_mem firstInduction secondInduction
  | smul scalar vector _ inductionHypothesis =>
    simpa only [LinearMap.map_smulₛₗ] using
      (grade D weight).smul_mem (starRingEnd ℂ scalar) inductionHypothesis

private theorem hermitian_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (charge : Charge D)
    (left right : Carrier D) (index : ℤ) :
    hermitianForm D (((Y D (Finsupp.single charge (1 : Oscillator D)))[[index]]) left) right =
      hermitianForm D left (oppositeCoeff D H (chargeEnergy D charge)
        (pct D (Finsupp.single charge (1 : Oscillator D))) index right) := by
  have reflection : pct D (Finsupp.single charge (1 : Oscillator D)) =
      Finsupp.single (-charge) (1 : Oscillator D) := by
    simp [pct, coefficientConjugation, LatticeOscillatorFockForm.conjugatePolynomial]
  have reflectedWeight : chargeEnergy D (-charge) = chargeEnergy D charge := by
    simp only [chargeEnergy, LatticeInvolution.bilinear_neg_neg]
  rw [stateField_ground, hermitian_charged, reflection, ← reflectedWeight,
    opposite_ground, reflectedWeight, LinearMap.smul_apply, map_smul, two_chargeEnergy]
  rfl

private theorem hermitian_current_step (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (degree : ℕ) (state : Carrier D) (weight : ℤ)
    (homogeneous : state ∈ grade D weight)
    (inductionHypothesis : ∀ (left right : Carrier D) (index : ℤ),
      hermitianForm D (((Y D state)[[index]]) left) right =
        hermitianForm D left (oppositeCoeff D H weight (pct D state) index right))
    (left right : Carrier D) (index : ℤ) :
    hermitianForm D (((Y D (neutralMode D current (-(degree : ℤ) - 1) state))[[index]]) left)
      right =
      hermitianForm D left (oppositeCoeff D H (weight + degree + 1)
        (pct D (neutralMode D current (-(degree : ℤ) - 1) state)) index right) := by
  classical
  have original := current_negative_insertion D current degree state left index
  let first : ℕ → Carrier D := fun offset =>
    ((degree + offset).choose degree : ℂ) •
      neutralMode D current (-(offset : ℤ) - degree - 1)
        (((Y D state)[[index + offset]]) left)
  let second : ℕ → Carrier D := fun offset =>
    ((degree + offset).choose degree : ℂ) •
      ((Y D state)[[index - offset - degree - 1]]) (neutralMode D current offset left)
  have firstTranspose : ∀ offset, hermitianForm D (first offset) right =
      hermitianForm D left
        (reversedFirstTerm D H current degree weight (pct D state) index right offset) := by
    intro offset
    have mode : -(-(offset : ℤ) - degree - 1) = offset + degree + 1 := by omega
    simp only [first, reversedFirstTerm, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, starRingEnd_apply, star_natCast,
      hermitian_neutral, mode, inductionHypothesis, smul_eq_mul, map_smul]
  have secondTranspose : ∀ offset, hermitianForm D (second offset) right =
      hermitianForm D left
        (reversedSecondTerm D H current degree weight (pct D state) index right offset) := by
    intro offset
    simp only [second, reversedSecondTerm, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, starRingEnd_apply, star_natCast,
      inductionHypothesis, hermitian_neutral, smul_eq_mul, map_smul]
  have firstSum := ((hermitianForm D).flip right).toAddMonoidHom.map_finsum original.1
  have secondSum := ((hermitianForm D).flip right).toAddMonoidHom.map_finsum original.2.1
  have reversedFirst := (hermitianForm D left).toAddMonoidHom.map_finsum
    (reversed_first_finite D H current degree weight (pct D state) index right)
  have reversedSecond := (hermitianForm D left).toAddMonoidHom.map_finsum
    (reversed_second_finite D H current degree weight (pct D state) index right)
  change hermitianForm D left (∑ᶠ offset,
    reversedFirstTerm D H current degree weight (pct D state) index right offset) =
      ∑ᶠ offset, hermitianForm D left
        (reversedFirstTerm D H current degree weight (pct D state) index right
          offset) at reversedFirst
  change hermitianForm D left (∑ᶠ offset,
    reversedSecondTerm D H current degree weight (pct D state) index right offset) =
      ∑ᶠ offset, hermitianForm D left
        (reversedSecondTerm D H current degree weight (pct D state) index right
          offset) at reversedSecond
  change hermitianForm D (∑ᶠ offset, first offset) right =
    ∑ᶠ offset, hermitianForm D (first offset) right at firstSum
  change hermitianForm D (∑ᶠ offset, second offset) right =
    ∑ᶠ offset, hermitianForm D (second offset) right at secondSum
  simp_rw [firstTranspose] at firstSum
  simp_rw [secondTranspose] at secondSum
  rw [← reversedFirst] at firstSum
  rw [← reversedSecond] at secondSum
  have oppositeNeg : oppositeCoeff D H (weight + degree + 1)
      (-(neutralMode D current (-(degree : ℤ) - 1) (pct D state))) index =
      -oppositeCoeff D H (weight + degree + 1)
        (neutralMode D current (-(degree : ℤ) - 1) (pct D state)) index :=
    (oppositeLinear D H (weight + degree + 1) index).map_neg _
  rw [original.2.2, pct_neutral, oppositeNeg, LinearMap.neg_apply,
    opposite_current_insertion D H hHG hGH current degree (pct D state) right
      weight index (pct_grade D state weight homogeneous)]
  change hermitianForm D ((∑ᶠ offset, first offset) +
    (-1 : ℂ)^degree • ∑ᶠ offset, second offset) right = _
  simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    starRingEnd_apply, star_pow, star_neg, star_one, map_neg,
    firstSum, secondSum, map_smul, pow_succ]
  module

private def wordWeight (D : LatticeData) (charge : Charge D) : List (Index D) → ℤ
  | [] => chargeEnergy D charge
  | coordinate :: tail => wordWeight D charge tail + coordinate.2 + 1

private theorem word_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (charge : Charge D) (word : List (Index D)) :
    Finsupp.single charge (word.map (fun coordinate => (X coordinate : Oscillator D))).prod ∈
      grade D (wordWeight D charge word) := by
  induction word with
  | nil => simpa [wordWeight, carrierBasis_apply, energy, oscillatorEnergy] using
      basis_grade D (charge, 0)
  | cons coordinate tail inductionHypothesis =>
    have insertion := current_insertion_grade D H hHG hGH coordinate.1 coordinate.2
      (Finsupp.single charge (tail.map (fun item => (X item : Oscillator D))).prod)
      (wordWeight D charge tail) inductionHypothesis
    simpa only [wordWeight, neutralMode_single, neutralPolynomialMode_negative,
      LinearMap.mulLeft_apply, List.map_cons, List.prod_cons] using insertion

private theorem word_adjoints (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (charge : Charge D) (word : List (Index D)) :
    let state := Finsupp.single charge (word.map (fun coordinate => (X coordinate : Oscillator
      D))).prod
    (∀ (left right : Carrier D) (index : ℤ),
      bpzForm D (((Y D state)[[index]]) left) right =
        bpzForm D left (oppositeCoeff D H (wordWeight D charge word) state index right)) ∧
    (∀ (left right : Carrier D) (index : ℤ),
      hermitianForm D (((Y D state)[[index]]) left) right =
        hermitianForm D left (oppositeCoeff D H (wordWeight D charge word) (pct D state) index
          right)) := by
  induction word with
  | nil => exact ⟨bpz_ground D H charge, hermitian_ground D H charge⟩
  | cons coordinate tail inductionHypothesis =>
    have homogeneous := word_grade D H hHG hGH charge tail
    constructor
    · intro left right index
      have insertion := bpz_current_step D H hHG hGH coordinate.1 coordinate.2 _ _
        homogeneous inductionHypothesis.1 left right index
      simpa only [wordWeight, neutralMode_single, neutralPolynomialMode_negative,
        LinearMap.mulLeft_apply, List.map_cons, List.prod_cons] using insertion
    · intro left right index
      have insertion := hermitian_current_step D H hHG hGH coordinate.1 coordinate.2 _ _
        homogeneous inductionHypothesis.2 left right index
      simpa only [wordWeight, neutralMode_single, neutralPolynomialMode_negative,
        LinearMap.mulLeft_apply, List.map_cons, List.prod_cons] using insertion

private theorem basis_adjoints (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (label : Label D) :
    (∀ (left right : Carrier D) (index : ℤ),
      bpzForm D (((Y D (carrierBasis D label))[[index]]) left) right =
        bpzForm D left (oppositeCoeff D H (energy D label) (carrierBasis D label) index right)) ∧
    (∀ (left right : Carrier D) (index : ℤ),
      hermitianForm D (((Y D (carrierBasis D label))[[index]]) left) right =
        hermitianForm D left (oppositeCoeff D H (energy D label)
          (pct D (carrierBasis D label)) index right)) := by
  classical
  have homogeneous := word_grade D H hHG hGH label.1 (occurrences D label.2)
  rw [occurrences_product] at homogeneous
  have matching : energy D label = wordWeight D label.1 (occurrences D label.2) := by
    by_contra different
    have impossible := (mem_grade_iff D _ _).mp homogeneous label different
    simpa using impossible
  have result := word_adjoints D H hHG hGH label.1 (occurrences D label.2)
  simpa only [occurrences_product, ← carrierBasis_apply, ← matching] using result

private theorem homogeneous_adjoints (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : Carrier D) (weight : ℤ) (homogeneous : state ∈ grade D weight) :
    (∀ (left right : Carrier D) (index : ℤ),
      bpzForm D (((Y D state)[[index]]) left) right =
        bpzForm D left (oppositeCoeff D H weight state index right)) ∧
    (∀ (left right : Carrier D) (index : ℤ),
      hermitianForm D (((Y D state)[[index]]) left) right =
        hermitianForm D left (oppositeCoeff D H weight (pct D state) index right)) := by
  classical
  rw [grade_eq_span] at homogeneous
  induction homogeneous using Submodule.span_induction with
  | mem vector membership =>
    obtain ⟨label, matching, rfl⟩ := membership
    change energy D label = weight at matching
    simpa only [matching] using basis_adjoints D H hHG hGH label
  | zero =>
    have oppositeZero (index : ℤ) : oppositeCoeff D H weight 0 index = 0 :=
      (oppositeLinear D H weight index).map_zero
    constructor <;> intros <;>
      simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, oppositeZero]
  | add first second _ _ firstInduction secondInduction =>
    have oppositeAdd (first second : Carrier D) :
        oppositeCoeff D H weight (first + second) =
          fun index => oppositeCoeff D H weight first index + oppositeCoeff D H weight second
            index := by
      funext index
      exact (oppositeLinear D H weight index).map_add first second
    constructor
    · intro left right index
      simp only [map_add, Pi.add_apply, LinearMap.add_apply,
        firstInduction.1, secondInduction.1, oppositeAdd]
    · intro left right index
      simp only [map_add, Pi.add_apply, LinearMap.add_apply,
        firstInduction.2, secondInduction.2, oppositeAdd]
  | smul scalar vector _ inductionHypothesis =>
    have oppositeSmul (coefficient : ℂ) (vector : Carrier D) (index : ℤ) :
        oppositeCoeff D H weight (coefficient • vector) index =
          coefficient • oppositeCoeff D H weight vector index :=
      (oppositeLinear D H weight index).map_smul coefficient vector
    constructor
    · intro left right index
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
        inductionHypothesis.1, oppositeSmul]
    · intro left right index
      simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply,
        LinearMap.smul_apply, inductionHypothesis.2, oppositeSmul]

theorem bpz_stateField_homogeneous (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state left right : Carrier D) (weight index : ℤ) (homogeneous : state ∈ grade D weight) :
    bpzForm D (((Y D state)[[index]]) left) right =
      bpzForm D left (oppositeCoeff D H weight state index right) :=
  (homogeneous_adjoints D H hHG hGH state weight homogeneous).1 left right index

theorem hermitian_stateField_homogeneous (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state left right : Carrier D) (weight index : ℤ) (homogeneous : state ∈ grade D weight) :
    hermitianForm D (((Y D state)[[index]]) left) right =
      hermitianForm D left (oppositeCoeff D H weight (pct D state) index right) :=
  (homogeneous_adjoints D H hHG hGH state weight homogeneous).2 left right index

theorem bpz_stateField_all (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state left right : Carrier D) (index : ℤ) :
    bpzForm D (((Y D state)[[index]]) left) right =
      ∑ weight ∈ stateEnergies D state,
        bpzForm D left (oppositeCoeff D H weight (gradeProjection D weight state) index right) := by
  classical
  conv_lhs => rw [← sum_gradeProjections D state]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro weight present
  exact bpz_stateField_homogeneous D H hHG hGH _ left right weight index
    (gradeProjection_mem D weight state)

theorem hermitian_stateField_all (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state left right : Carrier D) (index : ℤ) :
    hermitianForm D (((Y D state)[[index]]) left) right =
      ∑ weight ∈ stateEnergies D state,
        hermitianForm D left
          (oppositeCoeff D H weight (pct D (gradeProjection D weight state)) index right) := by
  classical
  conv_lhs => rw [← sum_gradeProjections D state]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro weight present
  exact hermitian_stateField_homogeneous D H hHG hGH _ left right weight index
    (gradeProjection_mem D weight state)

end
end D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
