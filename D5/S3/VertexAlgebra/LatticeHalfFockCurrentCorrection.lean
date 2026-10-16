/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source partial derivatives through the full charged finite correction. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection MvPolynomial
open scoped BigOperators

noncomputable section

def correctionLift (D : LatticeData) (charge : Charge D) :
    Oscillator D →ₗ[ℂ] CorrectionPolynomial D :=
  (basisMonomials (Index D) ℂ).constr ℂ
    (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent))

private theorem correctionLift_monomial (D : LatticeData) (charge : Charge D)
    (exponent : Index D →₀ ℕ) :
    correctionLift D charge (monomial exponent 1) =
      correctionWord D charge (LatticeAllStateField.occurrences D exponent) :=
  (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => correctionWord D charge (LatticeAllStateField.occurrences D exponent)) exponent

theorem occurrences_cons (D : LatticeData) (index : Index D) (exponent : Index D →₀ ℕ) :
    (index :: LatticeAllStateField.occurrences D exponent).Perm
      (LatticeAllStateField.occurrences D (exponent + Finsupp.single index 1)) := by
  apply Multiset.coe_eq_coe.mp
  simp [LatticeAllStateField.occurrences, Finsupp.toMultiset_add,
    Finsupp.toMultiset_single, ← Multiset.cons_coe, Multiset.coe_toList, add_comm]

theorem correctionLift_X_mul (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : Oscillator D) :
    correctionLift D charge (polynomial * X index) =
      insertion D charge index (correctionLift D charge polynomial) := by
  induction polynomial using MvPolynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [add_mul, map_add, firstProof, secondProof]
  | monomial exponent scalar =>
    have scale (exponent : Index D →₀ ℕ) :
        monomial exponent scalar = scalar • monomial exponent 1 := by
      simp [smul_monomial]
    rw [X, monomial_mul, mul_one, scale, map_smul, correctionLift_monomial,
      scale, map_smul, correctionLift_monomial, map_smul]
    congr 1
    exact correctionWord_permutation D charge _ _
      (occurrences_cons D index exponent).symm

private theorem partial_singleton (D : LatticeData) (charge : Charge D)
    (index other : Index D) :
    pderiv (some index) (singletonPolynomial D charge other) = 0 := by
  simp [singletonPolynomial, pderiv_X, Pi.single_apply, pderiv_mul,
    Derivation.leibniz_pow]

private theorem partial_pair (D : LatticeData) (index first second : Index D) :
    pderiv (some index) (pairPolynomial D first second) = 0 := by
  simp [pairPolynomial, pderiv_X, Pi.single_apply, pderiv_mul,
    Derivation.leibniz_pow]

private theorem partial_pairDerivation (D : LatticeData) (index other : Index D)
    (polynomial : CorrectionPolynomial D) :
    pderiv (some index) (pairDerivation D other polynomial) =
      pairDerivation D other (pderiv (some index) polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | mul_X polynomial coordinate previous =>
    have first : pderiv (some index) (pairDerivation D other (X coordinate)) = 0 := by
      cases coordinate with
      | none => simp [pairDerivation, mkDerivation_X]
      | some coordinate => simp [pairDerivation, mkDerivation_X, partial_pair]
    have second : pairDerivation D other (pderiv (some index) (X coordinate)) = 0 := by
      classical
      simp [pderiv_X, Pi.single_apply, apply_ite]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, first, second,
      mul_zero, zero_mul, add_zero, zero_add, previous]
    ring

private theorem partial_insertion (D : LatticeData) (charge : Charge D)
    (index other : Index D) (polynomial : CorrectionPolynomial D) :
    pderiv (some index) (insertion D charge other polynomial) =
      (if other = index then polynomial else 0) +
        insertion D charge other (pderiv (some index) polynomial) := by
  classical
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, pderiv_mul, partial_singleton,
    partial_pairDerivation, pderiv_X, Pi.single_apply, Option.some.injEq]
  split_ifs <;> ring

private theorem correctionLift_C (D : LatticeData) (charge : Charge D) (scalar : ℂ) :
    correctionLift D charge (C scalar) = C scalar := by
  rw [show C scalar = scalar • monomial (0 : Index D →₀ ℕ) 1 by
      simpa using (C_eq_smul_one (σ := Index D) (a := scalar)),
    map_smul, correctionLift_monomial]
  simp [LatticeAllStateField.occurrences, correctionWord, Algebra.smul_def]

theorem correctionLift_partial (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : Oscillator D) :
    pderiv (some index) (correctionLift D charge polynomial) =
      correctionLift D charge (pderiv index polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [correctionLift_C]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | mul_X polynomial other previous =>
    rw [correctionLift_X_mul, partial_insertion, previous, pderiv_mul]
    simp only [pderiv_X, Pi.single_apply, smul_eq_mul, map_add]
    rw [correctionLift_X_mul]
    by_cases same : other = index <;> simp [same, map_zero, add_comm]

private theorem optionEquivLeft_partial (D : LatticeData) (index : Index D)
    (polynomial : CorrectionPolynomial D) (shift : ℕ) :
    pderiv index ((optionEquivLeft ℂ (Index D) polynomial).coeff shift) =
      (optionEquivLeft ℂ (Index D) (pderiv (some index) polynomial)).coeff shift := by
  classical
  induction polynomial using MvPolynomial.induction_on generalizing shift with
  | C scalar => simp [optionEquivLeft_C, Polynomial.coeff_C, apply_ite]
  | add first second firstProof secondProof =>
    simp only [map_add, Polynomial.coeff_add, firstProof, secondProof]
  | mul_X polynomial coordinate previous =>
    cases coordinate with
    | none =>
      cases shift with
      | zero => simp [map_mul, optionEquivLeft_X_none, pderiv_mul, pderiv_X, Pi.single_apply]
      | succ shift =>
        simpa [map_mul, optionEquivLeft_X_none, pderiv_mul, pderiv_X,
          Pi.single_apply] using previous shift
    | some other =>
      simp only [map_mul, optionEquivLeft_X_some, Polynomial.coeff_mul_C,
        pderiv_mul, pderiv_X, Pi.single_apply, Option.some.injEq, smul_eq_mul,
        map_add, Polynomial.coeff_add, previous]
      by_cases same : other = index <;> simp [same]

theorem Corr_partial (D : LatticeData) (charge : Charge D) (index : Index D)
    (polynomial : Oscillator D) (shift : ℕ) :
    pderiv index (Corr D charge polynomial shift) =
      Corr D charge (pderiv index polynomial) shift := by
  have bridge := optionEquivLeft_partial D index (correctionLift D charge polynomial) shift
  rw [correctionLift_partial] at bridge
  simpa only [Corr, correctionPolynomial, correctionLift, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, shiftCoefficients, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.toFinsupp_apply] using bridge

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
