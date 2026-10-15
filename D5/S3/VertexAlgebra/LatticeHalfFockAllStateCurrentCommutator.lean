/- GID: D5/S3/VertexAlgebra/LatticeHalfFockAllStateCurrentCommutator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockAllStateCurrentCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite ordinary source modes and current calculus for corrected twisted lattice fields. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedCurrentAction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField
open LatticeHalfFockAllStateField LatticeHalfFockFirstDescendant
open LatticeHalfFockOriginalMixedIterate MvPolynomial
open LatticeHalfFockCurrentNormalRecurrence LatticeHalfFockNormalCurrentAction
open LatticeHalfFockCorrectedCurrentAction
open scoped BigOperators VertexOperator

noncomputable section

theorem sourceCurrent_single (D : LatticeData) (h : Fin D.rank → ℂ)
    (mode : ℤ) (charge : Charge D) (polynomial : Oscillator D) :
    ((sourceCurrent D h)[[mode]]) (Finsupp.single charge polynomial) =
      Finsupp.single charge
        (∑ colour, h colour • neutralPolynomialMode D colour charge mode polynomial) := by
  rw [sourceCurrent_mode]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, neutralMode_single,
    Finsupp.smul_single, Finsupp.single_finsetSum]

theorem sourceCurrent_upper_truncation (D : LatticeData) (h : Fin D.rank → ℂ)
    (state : Carrier D) (mode : ℤ) (above : (vectorFrequencyBound D state : ℤ) < mode) :
    ((sourceCurrent D h)[[mode]]) state = 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single state]
  simp only [Finsupp.sum, map_sum, sourceCurrent_single]
  apply Finset.sum_eq_zero
  intro charge member
  have bound := Finset.le_sup
    (f := fun charge => polynomialFrequencyBound D (state charge)) member
  have vanish (colour : Fin D.rank) :
      neutralPolynomialMode D colour charge mode (state charge) = 0 :=
    neutralPolynomialMode_vanish D colour charge (state charge) mode (by
      change polynomialFrequencyBound D (state charge) ≤ vectorFrequencyBound D state at bound
      omega)
  simp [vanish]

theorem sourceCurrent_nat_support (D : LatticeData) (h : Fin D.rank → ℂ)
    (state : Carrier D) :
    Function.support (fun degree : ℕ => ((sourceCurrent D h)[[(degree : ℤ)]]) state) ⊆
      Finset.range (vectorFrequencyBound D state + 1) := by
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  exact nonzero (sourceCurrent_upper_truncation D h state degree (by omega))

private def coefficientEvaluation (D : LatticeData) (hu : IsUnit D.G.det)
    (exponent : ℤ) (vector : ActualTensor D hu) :
    NativeField D hu →ₗ[ℂ] ActualTensor D hu where
  toFun field := field.coeff exponent vector
  map_add' first second := rfl
  map_smul' scalar field := rfl

private theorem Ytw_single_polynomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) :
    Ytw D hu (Finsupp.single charge polynomial) = correctedPolynomial D hu charge polynomial := by
  simp [Ytw]

private def neutralTerm (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (state : Carrier D) (mode exponent : ℤ) (vector : ActualTensor D hu) (degree : ℕ) :
    ActualTensor D hu :=
  Ring.choose (LatticeHalfFock.frequency mode) degree •
    (Ytw D hu (neutralMode D colour degree state)).coeff
      (exponent - (2 * mode + 1) + 2 * degree) vector

private theorem neutralTerm_support (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (state : Carrier D) (mode exponent : ℤ)
    (vector : ActualTensor D hu) :
    Function.support (neutralTerm D hu colour state mode exponent vector) ⊆
      Finset.range (vectorFrequencyBound D state + 1) := by
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  exact nonzero (by simp [neutralTerm, neutralMode_vanish D colour state degree (by omega)])

private theorem neutralTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (state : Carrier D) (mode exponent : ℤ)
    (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (neutralTerm D hu colour state mode exponent vector) :=
  (Finset.range (vectorFrequencyBound D state + 1)).finite_toSet.subset
    (neutralTerm_support D hu colour state mode exponent vector)

private theorem neutralTerm_add (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (first second : Carrier D) (mode exponent : ℤ)
    (vector : ActualTensor D hu) :
    (∑ᶠ degree : ℕ, neutralTerm D hu colour (first + second) mode exponent vector degree) =
      (∑ᶠ degree : ℕ, neutralTerm D hu colour first mode exponent vector degree) +
        ∑ᶠ degree : ℕ, neutralTerm D hu colour second mode exponent vector degree := by
  have terms : neutralTerm D hu colour (first + second) mode exponent vector =
      fun degree => neutralTerm D hu colour first mode exponent vector degree +
        neutralTerm D hu colour second mode exponent vector degree := by
    funext degree
    simp only [neutralTerm, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  rw [terms, finsum_add_distrib (neutralTerm_finite D hu colour first mode exponent vector)
    (neutralTerm_finite D hu colour second mode exponent vector)]

private theorem single_current_Ytw_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (charge : Charge D) (polynomial : Oscillator D)
    (mode exponent : ℤ) (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
        ((Ytw D hu (Finsupp.single charge polynomial)).coeff exponent vector) -
      (Ytw D hu (Finsupp.single charge polynomial)).coeff exponent
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector) =
      ∑ᶠ degree : ℕ,
        neutralTerm D hu colour (Finsupp.single charge polynomial) mode exponent vector degree := by
  have original := congrArg (fun operator : Module.End ℂ (ActualTensor D hu) => operator vector)
    (correctedPolynomial_current_commutator D hu charge colour mode exponent polynomial)
  have finite : Function.HasFiniteSupport (correctedDeltaTerm D hu charge colour mode polynomial) :=
    (Finset.range (polynomialFrequencyBound D polynomial + 1)).finite_toSet.subset
      (correctedDeltaTerm_support D hu charge colour mode polynomial)
  have mapped : (correctedDelta D hu charge colour mode polynomial).coeff exponent vector =
      ∑ᶠ degree : ℕ,
        (correctedDeltaTerm D hu charge colour mode polynomial degree).coeff exponent vector :=
    (coefficientEvaluation D hu exponent vector).toAddMonoidHom.map_finsum finite
  rw [Ytw_single_polynomial]
  change (LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
      (correctedPolynomial D hu charge polynomial).coeff exponent -
        (correctedPolynomial D hu charge polynomial).coeff exponent *
          LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode) vector = _
  rw [correctedPolynomial_current_commutator, mapped]
  apply finsum_congr
  intro degree
  simp only [neutralTerm, neutralMode_single, Ytw_single_polynomial]
  change Ring.choose (LatticeHalfFock.frequency mode) degree •
      (correctedPolynomial D hu charge
        (neutralPolynomialMode D colour charge degree polynomial)).coeff
          (exponent + (-(2 * mode + 1) + 2 * degree)) vector = _
  rw [show exponent + (-(2 * mode + 1) + 2 * (degree : ℤ)) =
    exponent - (2 * mode + 1) + 2 * degree by omega]

theorem neutral_current_Ytw_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (state : Carrier D) (mode exponent : ℤ)
    (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
        ((Ytw D hu state).coeff exponent vector) -
      (Ytw D hu state).coeff exponent
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector) =
      ∑ᶠ degree : ℕ, neutralTerm D hu colour state mode exponent vector degree := by
  induction state using Finsupp.induction_linear with
  | zero => simp [neutralTerm]
  | single charge polynomial =>
    exact single_current_Ytw_commutator D hu colour charge polynomial mode exponent vector
  | add first second firstProof secondProof =>
    rw [neutralTerm_add]
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    rw [← firstProof, ← secondProof]
    abel

theorem current_Ytw_rhs_support (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (mode exponent : ℤ)
    (vector : ActualTensor D hu) :
    Function.support (fun degree : ℕ =>
      Ring.choose (LatticeHalfFock.frequency mode) degree •
        (Ytw D hu (((sourceCurrent D h)[[(degree : ℤ)]]) state)).coeff
          (exponent - (2 * mode + 1) + 2 * degree) vector) ⊆
      Finset.range (vectorFrequencyBound D state + 1) := by
  intro degree nonzero
  apply sourceCurrent_nat_support D h state
  intro zero
  exact nonzero (by simp [zero])

theorem actual_current_Ytw_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (mode exponent : ℤ)
    (vector : ActualTensor D hu) :
    currentCombination D hu h mode ((Ytw D hu state).coeff exponent vector) -
      (Ytw D hu state).coeff exponent (currentCombination D hu h mode vector) =
      ∑ᶠ degree : ℕ, Ring.choose (LatticeHalfFock.frequency mode) degree •
        (Ytw D hu (((sourceCurrent D h)[[(degree : ℤ)]]) state)).coeff
          (exponent - (2 * mode + 1) + 2 * degree) vector := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (current_Ytw_rhs_support D hu h state mode exponent vector)]
  simp only [currentCombination, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
  simp_rw [neutral_current_Ytw_commutator D hu _ state mode exponent vector,
    finsum_eq_sum_of_support_subset _ (neutralTerm_support D hu _ state mode exponent vector)]
  simp only [sourceCurrent_mode, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum, neutralTerm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro degree member
  apply Finset.sum_congr rfl
  intro colour colourMember
  exact smul_comm _ _ _

end
end D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator.actual_current_Ytw_commutator
