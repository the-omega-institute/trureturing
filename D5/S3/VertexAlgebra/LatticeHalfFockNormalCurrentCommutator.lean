/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNormalCurrentCommutator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNormalCurrentCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite current commutation through every native normal-polynomial state. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField LatticeHalfFockCurrentCorrection
open LatticeHalfFockCurrentNormalRecurrence LatticeHalfFockNormalCurrentAction MvPolynomial
open scoped BigOperators

noncomputable section

theorem nativeDelta_X_mul (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (index : Index D) (polynomial : Oscillator D) :
    nativeDelta D hu charge colour mode (polynomial * X index) =
      normalInsertionLinear D hu index (nativeDelta D hu charge colour mode polynomial) +
        (LatticeHalfFock.frequency mode * jetScalar index.2 (-mode - 1) *
          (D.G colour index.1 : ℂ)) •
            coverShiftLinear D hu (-2 * mode + 2 * index.2 + 1)
              (normalPolynomial D hu charge polynomial) := by
  classical
  let extra : ℕ → NativeField D hu := fun degree =>
    if degree = index.2 + 1 then
      (LatticeHalfFock.frequency mode * jetScalar index.2 (-mode - 1) *
        (D.G colour index.1 : ℂ)) •
          coverShiftLinear D hu (-2 * mode + 2 * index.2 + 1)
            (normalPolynomial D hu charge polynomial) else 0
  have extraFinite : Function.HasFiniteSupport extra := by
    apply ({index.2 + 1} : Finset ℕ).finite_toSet.subset
    intro degree member
    by_contra outside
    apply member
    simp only [Finset.mem_coe, Finset.mem_singleton] at outside
    simp [extra, outside]
  have terms (degree : ℕ) : deltaTerm D hu charge colour mode (polynomial * X index) degree =
      normalInsertionLinear D hu index (deltaTerm D hu charge colour mode polynomial degree) +
        extra degree := by
    unfold deltaTerm
    rw [neutralPolynomialMode_X_mul, map_add, map_add, smul_add,
      normalPolynomial_X_mul]
    have insertionShift (field : NativeField D hu) :
        coverShiftLinear D hu (-(2 * mode + 1) + 2 * degree)
            (normalInsertionLinear D hu index field) =
          normalInsertionLinear D hu index
            (coverShiftLinear D hu (-(2 * mode + 1) + 2 * degree) field) :=
      (normalInsertion_coverShift D hu index field (-(2 * mode + 1) + 2 * degree)).symm
    rw [insertionShift, ← map_smul]
    congr 1
    by_cases exceptional : degree = index.2 + 1
    · subst degree
      simp only [if_pos rfl, ite_true, map_smul, smul_smul, extra, jet_contraction_binomial,
        Nat.cast_add, Nat.cast_one]
      rw [show -(2 * mode + 1) + 2 * ((index.2 : ℤ) + 1) =
        -2 * mode + 2 * index.2 + 1 by omega]
      congr 1
      ring
    · simp only [if_neg exceptional, map_zero, smul_zero, extra]
  rw [nativeDelta]
  simp_rw [terms]
  rw [finsum_add_distrib
    ((deltaTerm_finite D hu charge colour mode polynomial).fun_comp
      (map_zero (normalInsertionLinear D hu index))) extraFinite]
  have mapped : (∑ᶠ degree : ℕ,
        normalInsertionLinear D hu index (deltaTerm D hu charge colour mode polynomial degree)) =
      normalInsertionLinear D hu index (nativeDelta D hu charge colour mode polynomial) :=
    ((normalInsertionLinear D hu index).toAddMonoidHom.map_finsum
      (deltaTerm_finite D hu charge colour mode polynomial)).symm
  rw [mapped, finsum_eq_single _ (index.2 + 1)]
  · simp [extra]
  · intro degree outside
    simp [extra, outside]

private theorem normalPolynomial_C (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (scalar : ℂ) :
    normalPolynomial D hu charge (C scalar) = scalar • chargedField D hu charge := by
  rw [C_eq_smul_one, map_smul, normalPolynomial_one]

private theorem nativeDelta_C (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (colour : Fin D.rank) (mode : ℤ) (scalar : ℂ) :
    nativeDelta D hu charge colour mode (C scalar) =
      (bilinear D (unitCharge D colour) charge : ℂ) •
        coverShiftLinear D hu (-(2 * mode + 1)) (normalPolynomial D hu charge (C scalar)) := by
  rw [nativeDelta, finsum_eq_single _ 0]
  · simp [deltaTerm, neutralPolynomialMode]
  · intro degree outside
    have high : (polynomialFrequencyBound D (C scalar : Oscillator D) : ℤ) < degree := by
      simp only [polynomialFrequencyBound, MvPolynomial.vars_C, Finset.sup_empty]
      exact_mod_cast Nat.pos_of_ne_zero outside
    simp [deltaTerm, neutralPolynomialMode_vanish D colour charge (C scalar) degree high]

private theorem commutator_add {Algebra : Type*} [Ring Algebra]
    (current first second : Algebra) :
    current * (first + second) - (first + second) * current =
      (current * first - first * current) + (current * second - second * current) := by
  noncomm_ring

theorem normalPolynomial_current_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (colour : Fin D.rank) (mode : ℤ) (polynomial : Oscillator D) :
    ∀ exponent : ℤ,
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
          (normalPolynomial D hu charge polynomial).coeff exponent -
        (normalPolynomial D hu charge polynomial).coeff exponent *
          LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
        (nativeDelta D hu charge colour mode polynomial).coeff exponent := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    intro exponent
    rw [nativeDelta_C, normalPolynomial_C]
    change LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
        (scalar • chargedCoefficient D hu charge exponent) -
      (scalar • chargedCoefficient D hu charge exponent) *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
      (bilinear D (unitCharge D colour) charge : ℂ) •
        (scalar • chargedCoefficient D hu charge (exponent + -(2 * mode + 1)))
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, charged_tensor_current_ward]
    rw [show exponent + -(2 * mode + 1) = exponent - (2 * mode + 1) by omega]
    exact smul_comm _ _ _
  | add first second firstProof secondProof =>
    intro exponent
    rw [map_add, nativeDelta_add]
    change LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
        ((normalPolynomial D hu charge first).coeff exponent +
          (normalPolynomial D hu charge second).coeff exponent) -
      ((normalPolynomial D hu charge first).coeff exponent +
          (normalPolynomial D hu charge second).coeff exponent) *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
      (nativeDelta D hu charge colour mode first).coeff exponent +
        (nativeDelta D hu charge colour mode second).coeff exponent
    rw [commutator_add, firstProof, secondProof]
  | mul_X polynomial index previous =>
    intro exponent
    rw [normalPolynomial_X_mul, nativeDelta_X_mul]
    apply LinearMap.ext
    intro vector
    change LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
        ((normalInsertion D hu index (normalPolynomial D hu charge polynomial)).coeff exponent vector) -
      (normalInsertion D hu index (normalPolynomial D hu charge polynomial)).coeff exponent
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector) =
      (normalInsertion D hu index (nativeDelta D hu charge colour mode polynomial)).coeff exponent vector +
        (LatticeHalfFock.frequency mode * jetScalar index.2 (-mode - 1) *
          (D.G colour index.1 : ℂ)) •
            (normalPolynomial D hu charge polynomial).coeff
              (exponent + (-2 * mode + 2 * index.2 + 1)) vector
    rw [show exponent + (-2 * mode + 2 * (index.2 : ℤ) + 1) =
      exponent - 2 * mode + 2 * index.2 + 1 by omega]
    exact normalInsertion_current_commutator D hu colour mode exponent index
      (normalPolynomial D hu charge polynomial) (nativeDelta D hu charge colour mode polynomial)
      previous vector

end
end D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator
