/- GID: D5/S3/VertexAlgebra/LatticeOscillatorFockForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeOscillatorFockForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constant-term contraction form on the actual lattice oscillator. -/

/-
admission_basis: escape-witness
escape_witness: annihilatorEvaluation_reverse_creator derives the full actual
finite-word creator commutator for arbitrary polynomial occupations. Its
constant-term consumer gramBilinear_creator_right supplies the reverse
adjoint and Hermitian symmetry without an assumed invariant-form record.
proof_shape: fockForm_isSymm: content
proof_shape: fockForm_annihilation_adjoint: content
proof_shape: fockForm_energy_orthogonal: content
proof_shape: fockForm_unique: content
proof_shape: fockForm_vacuum_left: bind-only; consumed by fockForm_unique and
the original-owner Reg dependence proof.
proof_shape: fockForm_creation_adjoint: bind-only; consumed by fockForm_unique.
All private organization helpers have actual local proof consumers. Standard
Heisenberg contravariance and this carrier application carry zero novelty.
No inverse Gram, positivity, ghost pairing or physical quotient is assumed.
-/

import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finset.NoncommProd
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOscillatorFockForm

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open MvPolynomial
open scoped BigOperators

noncomputable section

def annihilator (D : LatticeData) (coordinate : Index D) :
    Module.End ℂ (Oscillator D) :=
  (coordinate.2 + 1 : ℂ) • weightedPartial D coordinate.1 coordinate.2

def contraction (D : LatticeData) (left right : Index D) : ℂ :=
  if left.2 = right.2 then
    (left.2 + 1 : ℂ) * (D.G left.1 right.1 : ℂ) else 0

private theorem annihilator_commute (D : LatticeData) (left right : Index D) :
    Commute (annihilator D left) (annihilator D right) := by
  have identity := neutralPolynomialMode_heisenberg D left.1 right.1 0
    ((left.2 : ℤ) + 1) ((right.2 : ℤ) + 1)
  have nonzero : (left.2 : ℤ) + 1 + ((right.2 : ℤ) + 1) ≠ 0 := by omega
  rw [if_neg nonzero, zero_smul, neutralPolynomialMode_positive,
    neutralPolynomialMode_positive] at identity
  exact sub_eq_zero.mp identity

private theorem annihilator_X_mul (D : LatticeData) (left right : Index D)
    (polynomial : Oscillator D) :
    annihilator D left (X right * polynomial) =
      X right * annihilator D left polynomial + contraction D left right • polynomial := by
  have identity := neutralPolynomialMode_heisenberg D left.1 right.1 0
    ((left.2 : ℤ) + 1) (-(right.2 : ℤ) - 1)
  have frequency : (left.2 : ℤ) + 1 + (-(right.2 : ℤ) - 1) = 0 ↔
      left.2 = right.2 := by omega
  rw [neutralPolynomialMode_positive, neutralPolynomialMode_negative] at identity
  have applied := congrArg (fun operator : Module.End ℂ (Oscillator D) =>
    operator polynomial) identity
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, Module.End.one_apply, frequency, Int.cast_add,
    Int.cast_natCast, Int.cast_one] at applied
  exact (sub_eq_iff_eq_add.mp applied).trans (add_comm _ _)

private theorem annihilator_constant (D : LatticeData) (coordinate : Index D)
    (scalar : ℂ) : annihilator D coordinate (C scalar) = 0 := by
  simp [annihilator, weightedPartial, LinearMap.sum_apply,
    LinearMap.smul_apply, Derivation.coeFn_coe]

private theorem annihilator_pairwise (D : LatticeData)
    (word : Multiset (Index D)) :
    {operator | operator ∈ word.map (annihilator D)}.Pairwise Commute := by
  intro left left_mem right right_mem different
  obtain ⟨left_coordinate, _, rfl⟩ := Multiset.mem_map.mp left_mem
  obtain ⟨right_coordinate, _, rfl⟩ := Multiset.mem_map.mp right_mem
  exact annihilator_commute D left_coordinate right_coordinate

private def annihilatorWord (D : LatticeData) (word : Multiset (Index D)) :
    Module.End ℂ (Oscillator D) :=
  (word.map (annihilator D)).noncommProd (annihilator_pairwise D word)

private theorem annihilatorWord_cons (D : LatticeData) (word : Multiset (Index D))
    (coordinate : Index D) :
    annihilatorWord D (coordinate ::ₘ word) =
      annihilatorWord D word * annihilator D coordinate := by
  have pairwise : {operator | operator ∈
      annihilator D coordinate ::ₘ word.map (annihilator D)}.Pairwise Commute := by
    simpa only [Multiset.map_cons] using annihilator_pairwise D (coordinate ::ₘ word)
  simpa only [annihilatorWord, Multiset.map_cons] using
    Multiset.noncommProd_cons' (word.map (annihilator D)) (annihilator D coordinate) pairwise

def annihilatorProduct (D : LatticeData) (occupation : Index D →₀ ℕ) :
    Module.End ℂ (Oscillator D) :=
  annihilatorWord D occupation.toMultiset

private theorem annihilatorProduct_zero (D : LatticeData) :
    annihilatorProduct D 0 = 1 := by
  simp [annihilatorProduct, annihilatorWord]

private theorem annihilatorProduct_insert (D : LatticeData)
    (occupation : Index D →₀ ℕ) (coordinate : Index D) :
    annihilatorProduct D (occupation + Finsupp.single coordinate 1) =
      annihilatorProduct D occupation * annihilator D coordinate := by
  unfold annihilatorProduct
  rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul,
    Multiset.add_comm, Multiset.singleton_add, annihilatorWord_cons]

private def annihilatorEvaluation (D : LatticeData) :
    Oscillator D →ₗ[ℂ] Module.End ℂ (Oscillator D) :=
  (basisMonomials (Index D) ℂ).constr ℂ (annihilatorProduct D)

private theorem annihilatorEvaluation_monomial (D : LatticeData)
    (occupation : Index D →₀ ℕ) :
    annihilatorEvaluation D (monomial occupation 1) = annihilatorProduct D occupation := by
  exact (basisMonomials (Index D) ℂ).constr_basis ℂ _ occupation

private theorem annihilatorEvaluation_coefficient (D : LatticeData)
    (occupation : Index D →₀ ℕ) (scalar : ℂ) :
    annihilatorEvaluation D (monomial occupation scalar) =
      scalar • annihilatorProduct D occupation := by
  have identity : (monomial occupation scalar : Oscillator D) =
      scalar • monomial occupation 1 := by simp [smul_monomial]
  rw [identity, map_smul, annihilatorEvaluation_monomial]

private theorem annihilatorEvaluation_constant (D : LatticeData) (scalar : ℂ) :
    annihilatorEvaluation D (C scalar) = scalar • (1 : Module.End ℂ (Oscillator D)) := by
  rw [← monomial_zero', annihilatorEvaluation_coefficient, annihilatorProduct_zero]

private theorem annihilatorEvaluation_creator (D : LatticeData) (coordinate : Index D)
    (polynomial : Oscillator D) :
    annihilatorEvaluation D (X coordinate * polynomial) =
      annihilatorEvaluation D polynomial * annihilator D coordinate := by
  have identity : (annihilatorEvaluation D).comp (LinearMap.mulLeft ℂ (X coordinate)) =
      (LinearMap.mulRight ℂ (annihilator D coordinate)).comp (annihilatorEvaluation D) := by
    apply (basisMonomials (Index D) ℂ).ext
    intro occupation
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      coe_basisMonomials]
    have monomial_step : X coordinate * monomial occupation (1 : ℂ) =
        monomial (occupation + Finsupp.single coordinate 1) 1 := by
      simpa [mul_comm] using
        (monomial_add_single (s := occupation) (n := coordinate) (e := 1) (a := (1 : ℂ))).symm
    rw [monomial_step, annihilatorEvaluation_monomial, annihilatorEvaluation_monomial,
      annihilatorProduct_insert]
  exact congrArg (fun operator => operator polynomial) identity

def gramBilinear (D : LatticeData) :
    Oscillator D →ₗ[ℂ] Oscillator D →ₗ[ℂ] ℂ :=
  (basisMonomials (Index D) ℂ).constr ℂ (fun occupation =>
    (lcoeff ℂ 0).comp (annihilatorProduct D occupation))

private theorem gramBilinear_monomial (D : LatticeData)
    (occupation : Index D →₀ ℕ) (polynomial : Oscillator D) :
    gramBilinear D (monomial occupation 1) polynomial =
      constantCoeff (annihilatorProduct D occupation polynomial) := by
  exact congrArg (fun functional : Oscillator D →ₗ[ℂ] ℂ => functional polynomial)
    ((basisMonomials (Index D) ℂ).constr_basis ℂ
      (fun exponent => (lcoeff ℂ 0).comp (annihilatorProduct D exponent)) occupation)

private theorem gramBilinear_one_left (D : LatticeData) (polynomial : Oscillator D) :
    gramBilinear D 1 polynomial = constantCoeff polynomial := by
  rw [one_def, gramBilinear_monomial, annihilatorProduct_zero]
  rfl

private theorem gramBilinear_constant_left (D : LatticeData) (scalar : ℂ)
    (polynomial : Oscillator D) :
    gramBilinear D (C scalar) polynomial = scalar * constantCoeff polynomial := by
  rw [C_eq_smul_one, map_smul, LinearMap.smul_apply, gramBilinear_one_left]
  rfl

private theorem gramBilinear_creator_left (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    gramBilinear D (X coordinate * left) right =
      gramBilinear D left (annihilator D coordinate right) := by
  have identity :
      (gramBilinear D).comp (LinearMap.mulLeft ℂ (X coordinate)) =
        (LinearMap.compl₂ (gramBilinear D) (annihilator D coordinate)) := by
    apply (basisMonomials (Index D) ℂ).ext
    intro occupation
    apply LinearMap.ext
    intro polynomial
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.compl₂_apply,
      coe_basisMonomials]
    have monomial_step : X coordinate * monomial occupation (1 : ℂ) =
        monomial (occupation + Finsupp.single coordinate 1) 1 := by
      simpa [mul_comm] using
        (monomial_add_single (s := occupation) (n := coordinate) (e := 1) (a := (1 : ℂ))).symm
    rw [monomial_step,
      gramBilinear_monomial, gramBilinear_monomial, annihilatorProduct_insert]
    rfl
  exact congrArg (fun form => form left right) identity

private theorem contraction_symmetric (D : LatticeData) (left right : Index D) :
    contraction D left right = contraction D right left := by
  unfold contraction
  by_cases frequency : left.2 = right.2
  · simp [frequency, D.symmetric]
  · simp [frequency, Ne.symm frequency]

private theorem annihilatorEvaluation_reverse_creator (D : LatticeData)
    (coordinate : Index D) (left right : Oscillator D) :
    annihilatorEvaluation D left (X coordinate * right) =
      X coordinate * annihilatorEvaluation D left right +
        annihilatorEvaluation D (annihilator D coordinate left) right := by
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      simp [annihilatorEvaluation_constant, annihilator_constant,
        LinearMap.smul_apply, mul_smul_comm]
  | add first second first_induction second_induction =>
      simp only [map_add, LinearMap.add_apply, first_induction, second_induction, mul_add]
      <;> abel
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator)]
      simp only [annihilatorEvaluation_creator, Module.End.mul_apply,
        annihilator_X_mul, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, induction_hypothesis]
      rw [contraction_symmetric D generator coordinate] <;> abel

private theorem gramBilinear_evaluation (D : LatticeData) (left right : Oscillator D) :
    gramBilinear D left right = constantCoeff (annihilatorEvaluation D left right) := by
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      simp [gramBilinear_constant_left, annihilatorEvaluation_constant,
        LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul]
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator), gramBilinear_creator_left,
        annihilatorEvaluation_creator, Module.End.mul_apply, induction_hypothesis]

private theorem annihilatorProduct_reverse_creator (D : LatticeData)
    (occupation : Index D →₀ ℕ) (coordinate : Index D) (polynomial : Oscillator D) :
    annihilatorProduct D occupation (X coordinate * polynomial) =
      X coordinate * annihilatorProduct D occupation polynomial +
        ∑ axis : Fin D.rank,
          ((coordinate.2 + 1 : ℂ) * (D.G coordinate.1 axis : ℂ) *
            (occupation (axis, coordinate.2) : ℂ)) •
              annihilatorProduct D (occupation - Finsupp.single (axis, coordinate.2) 1)
                polynomial := by
  have identity := annihilatorEvaluation_reverse_creator D coordinate
    (monomial occupation 1) polynomial
  rw [annihilatorEvaluation_monomial] at identity
  rw [identity]
  congr 1
  simp [annihilator, weightedPartial, LinearMap.smul_apply, LinearMap.sum_apply,
    Derivation.coeFn_coe, pderiv_monomial, map_sum, map_smul,
    annihilatorEvaluation_coefficient, Finset.smul_sum, smul_smul, mul_assoc]

private theorem gramBilinear_creator_right (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    gramBilinear D left (X coordinate * right) =
      gramBilinear D (annihilator D coordinate left) right := by
  have identity : (gramBilinear D).compl₂ (LinearMap.mulLeft ℂ (X coordinate)) =
      (gramBilinear D).comp (annihilator D coordinate) := by
    apply (basisMonomials (Index D) ℂ).ext
    intro occupation
    apply LinearMap.ext
    intro polynomial
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.mulLeft_apply,
      coe_basisMonomials]
    rw [gramBilinear_evaluation, gramBilinear_evaluation,
      annihilatorEvaluation_monomial, annihilatorProduct_reverse_creator]
    simp [annihilator, weightedPartial, LinearMap.smul_apply, LinearMap.sum_apply,
      Derivation.coeFn_coe, pderiv_monomial, map_sum, map_smul,
      annihilatorEvaluation_coefficient, Finset.smul_sum, smul_smul, mul_assoc]
  exact congrArg (fun form => form left right) identity

private theorem gramBilinear_one_right (D : LatticeData) (polynomial : Oscillator D) :
    gramBilinear D polynomial 1 = constantCoeff polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [gramBilinear_constant_left]
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator), gramBilinear_creator_left]
      have zero : annihilator D generator (1 : Oscillator D) = 0 :=
        annihilator_constant D generator 1
      simp [zero]

private theorem gramBilinear_symmetric (D : LatticeData) (left right : Oscillator D) :
    gramBilinear D left right = gramBilinear D right left := by
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      rw [gramBilinear_constant_left, C_eq_smul_one, map_smul, gramBilinear_one_right]
      rfl
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator), gramBilinear_creator_left,
        induction_hypothesis, gramBilinear_creator_right]

def conjugatePolynomial (D : LatticeData) : Oscillator D →ₗ⋆[ℂ] Oscillator D where
  toFun := MvPolynomial.map (starRingEnd ℂ)
  map_add' := by intro left right; exact map_add _ left right
  map_smul' := by
    intro scalar polynomial
    simp [MvPolynomial.smul_eq_C_mul]

private theorem conjugatePolynomial_involution (D : LatticeData)
    (polynomial : Oscillator D) :
    conjugatePolynomial D (conjugatePolynomial D polynomial) = polynomial := by
  apply MvPolynomial.ext
  intro occupation
  simp [conjugatePolynomial, coeff_map]

theorem conjugatePolynomial_X_mul (D : LatticeData)
    (coordinate : Index D) (polynomial : Oscillator D) :
    conjugatePolynomial D (X coordinate * polynomial) =
      X coordinate * conjugatePolynomial D polynomial := by
  simp [conjugatePolynomial]

theorem annihilator_conjugate (D : LatticeData) (coordinate : Index D)
    (polynomial : Oscillator D) :
    conjugatePolynomial D (annihilator D coordinate polynomial) =
      annihilator D coordinate (conjugatePolynomial D polynomial) := by
  simp [conjugatePolynomial, annihilator, weightedPartial, LinearMap.smul_apply,
    LinearMap.sum_apply, Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, pderiv_map]

private theorem gramBilinear_conjugate (D : LatticeData) (left right : Oscillator D) :
    star (gramBilinear D left right) =
      gramBilinear D (conjugatePolynomial D left) (conjugatePolynomial D right) := by
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      simp [gramBilinear_constant_left, conjugatePolynomial, constantCoeff_map]
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator), gramBilinear_creator_left,
        induction_hypothesis, annihilator_conjugate, conjugatePolynomial_X_mul,
        gramBilinear_creator_left]

def fockForm (D : LatticeData) : Oscillator D →ₗ⋆[ℂ] Oscillator D →ₗ[ℂ] ℂ :=
  (gramBilinear D).comp (conjugatePolynomial D)

theorem fockForm_vacuum_left (D : LatticeData) (polynomial : Oscillator D) :
    fockForm D 1 polynomial = constantCoeff polynomial := by
  change gramBilinear D (conjugatePolynomial D 1) polynomial = _
  simpa [conjugatePolynomial] using gramBilinear_one_left D polynomial

theorem fockForm_creator (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    fockForm D (X coordinate * left) right =
      fockForm D left (annihilator D coordinate right) := by
  change gramBilinear D (conjugatePolynomial D (X coordinate * left)) right = _
  rw [conjugatePolynomial_X_mul, gramBilinear_creator_left]
  rfl

theorem fockForm_creation_adjoint (D : LatticeData) (charge : Charge D)
    (axis : Fin D.rank) (frequency : ℕ) (left right : Oscillator D) :
    fockForm D (neutralPolynomialMode D axis charge (-(frequency : ℤ) - 1) left) right =
      fockForm D left (neutralPolynomialMode D axis charge ((frequency : ℤ) + 1) right) := by
  rw [neutralPolynomialMode_negative, neutralPolynomialMode_positive]
  exact fockForm_creator D (axis, frequency) left right

theorem fockForm_isSymm (D : LatticeData) : LinearMap.IsSymm (fockForm D) := by
  constructor
  intro left right
  change star (gramBilinear D (conjugatePolynomial D left) right) =
    gramBilinear D (conjugatePolynomial D right) left
  rw [gramBilinear_conjugate, conjugatePolynomial_involution, gramBilinear_symmetric]

theorem fockForm_annihilation_adjoint (D : LatticeData) (charge : Charge D)
    (axis : Fin D.rank) (frequency : ℕ) (left right : Oscillator D) :
    fockForm D (neutralPolynomialMode D axis charge ((frequency : ℤ) + 1) left) right =
      fockForm D left (neutralPolynomialMode D axis charge (-(frequency : ℤ) - 1) right) := by
  rw [neutralPolynomialMode_positive, neutralPolynomialMode_negative]
  change gramBilinear D (conjugatePolynomial D (annihilator D (axis, frequency) left))
    right = gramBilinear D (conjugatePolynomial D left) (X (axis, frequency) * right)
  rw [annihilator_conjugate, gramBilinear_creator_right]

private def energyScale (D : LatticeData) : Oscillator D →ₐ[ℂ] Oscillator D :=
  aeval (fun coordinate : Index D => (2 : ℂ) ^ (coordinate.2 + 1) • X coordinate)

private theorem energyScale_X_mul (D : LatticeData) (coordinate : Index D)
    (polynomial : Oscillator D) :
    energyScale D (X coordinate * polynomial) =
      (2 : ℂ) ^ (coordinate.2 + 1) • (X coordinate * energyScale D polynomial) := by
  simp [energyScale, smul_mul_assoc]

private theorem energyScale_constantCoeff (D : LatticeData) (polynomial : Oscillator D) :
    constantCoeff (energyScale D polynomial) = constantCoeff polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [energyScale]
  | add first second first_induction second_induction =>
      simp [map_add, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator), energyScale_X_mul]
      simp [MvPolynomial.smul_eq_C_mul]

private theorem contraction_energy (D : LatticeData) (left right : Index D) :
    (2 : ℂ) ^ (left.2 + 1) * contraction D left right =
      (2 : ℂ) ^ (right.2 + 1) * contraction D left right := by
  unfold contraction
  by_cases frequency : left.2 = right.2 <;> simp [frequency]

private theorem annihilator_energyScale (D : LatticeData) (coordinate : Index D)
    (polynomial : Oscillator D) :
    annihilator D coordinate (energyScale D polynomial) =
      (2 : ℂ) ^ (coordinate.2 + 1) •
        energyScale D (annihilator D coordinate polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [energyScale, annihilator_constant]
  | add first second first_induction second_induction =>
      simp [map_add, first_induction, second_induction, smul_add]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator), energyScale_X_mul, map_smul,
        annihilator_X_mul, induction_hypothesis, annihilator_X_mul,
        map_add, map_smul, energyScale_X_mul]
      simp only [smul_add, mul_smul_comm, smul_smul]
      rw [contraction_energy]
      congr 1
      rw [mul_comm]

private theorem gramBilinear_energyScale (D : LatticeData) (left right : Oscillator D) :
    gramBilinear D (energyScale D left) right =
      gramBilinear D left (energyScale D right) := by
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      have fixed : energyScale D (C scalar) = C scalar := by simp [energyScale]
      simp only [fixed, gramBilinear_constant_left, energyScale_constantCoeff]
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      rw [mul_comm polynomial (X generator)]
      have left_scaled : gramBilinear D (energyScale D (X generator * polynomial)) right =
          (2 : ℂ) ^ (generator.2 + 1) *
            gramBilinear D (energyScale D polynomial) (annihilator D generator right) := by
        rw [energyScale_X_mul]
        simp only [map_smul, LinearMap.smul_apply, gramBilinear_creator_left, smul_eq_mul]
      have right_scaled : gramBilinear D (X generator * polynomial) (energyScale D right) =
          (2 : ℂ) ^ (generator.2 + 1) *
            gramBilinear D polynomial (energyScale D (annihilator D generator right)) := by
        rw [gramBilinear_creator_left, annihilator_energyScale]
        simp only [map_smul, smul_eq_mul]
      rw [left_scaled, right_scaled, induction_hypothesis]

private theorem occupationEnergy_sum (D : LatticeData) (occupation : Index D →₀ ℕ) :
    (∑ coordinate ∈ occupation.support, (coordinate.2 + 1) * occupation coordinate) =
      Finsupp.weight (fun coordinate : Index D => coordinate.2 + 1) occupation := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro coordinate present
  simpa only [smul_eq_mul] using Nat.mul_comm (coordinate.2 + 1) (occupation coordinate)

private theorem energyScale_monomial (D : LatticeData) (occupation : Index D →₀ ℕ) :
    energyScale D (monomial occupation 1) =
      (2 : ℂ) ^ Finsupp.weight (fun coordinate : Index D => coordinate.2 + 1) occupation •
        monomial occupation 1 := by
  classical
  rw [energyScale, aeval_monomial]
  simp only [map_one, one_mul, Finsupp.prod]
  simp_rw [smul_pow, ← pow_mul]
  rw [Finset.prod_smul, Finset.prod_pow_eq_pow_sum, monic_monomial_eq, Finsupp.prod]
  rw [occupationEnergy_sum]

private theorem energyScale_homogeneous (D : LatticeData) (polynomial : Oscillator D)
    (energy : ℕ)
    (homogeneous : IsWeightedHomogeneous (fun coordinate : Index D => coordinate.2 + 1)
      polynomial energy) :
    energyScale D polynomial = (2 : ℂ) ^ energy • polynomial := by
  classical
  conv_lhs => rw [polynomial.as_sum]
  conv_rhs => rw [polynomial.as_sum]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro occupation present
  have coefficient_nonzero : coeff occupation polynomial ≠ 0 := mem_support_iff.mp present
  have degree := homogeneous coefficient_nonzero
  have coefficient_monomial : monomial occupation (coeff occupation polynomial) =
      coeff occupation polynomial • (monomial occupation 1 : Oscillator D) := by
    simp [smul_monomial]
  rw [coefficient_monomial, map_smul, energyScale_monomial, degree, smul_comm]

private theorem conjugatePolynomial_homogeneous (D : LatticeData)
    (polynomial : Oscillator D) (energy : ℕ)
    (homogeneous : IsWeightedHomogeneous (fun coordinate : Index D => coordinate.2 + 1)
      polynomial energy) :
    IsWeightedHomogeneous (fun coordinate : Index D => coordinate.2 + 1)
      (conjugatePolynomial D polynomial) energy := by
  intro occupation nonzero
  apply homogeneous
  intro zero
  apply nonzero
  simp [conjugatePolynomial, coeff_map, zero]

theorem fockForm_energy_orthogonal (D : LatticeData) (left right : Oscillator D)
    (left_energy right_energy : ℕ)
    (left_homogeneous : IsWeightedHomogeneous
      (fun coordinate : Index D => coordinate.2 + 1) left left_energy)
    (right_homogeneous : IsWeightedHomogeneous
      (fun coordinate : Index D => coordinate.2 + 1) right right_energy)
    (different : left_energy ≠ right_energy) : fockForm D left right = 0 := by
  have identity := gramBilinear_energyScale D (conjugatePolynomial D left) right
  rw [energyScale_homogeneous D _ left_energy
      (conjugatePolynomial_homogeneous D left left_energy left_homogeneous),
    energyScale_homogeneous D right right_energy right_homogeneous,
    map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at identity
  have powers_different : (2 : ℂ) ^ left_energy ≠ (2 : ℂ) ^ right_energy := by
    exact_mod_cast (Nat.pow_right_injective (a := 2) (by decide)).ne different
  have zero : ((2 : ℂ) ^ left_energy - (2 : ℂ) ^ right_energy) *
      gramBilinear D (conjugatePolynomial D left) right = 0 := by
    rw [sub_mul, identity, sub_self]
  exact (mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr powers_different)

theorem fockForm_unique (D : LatticeData)
    (candidate : Oscillator D →ₗ⋆[ℂ] Oscillator D →ₗ[ℂ] ℂ)
    (vacuum : ∀ polynomial, candidate 1 polynomial = constantCoeff polynomial)
    (adjoint : ∀ (coordinate : Index D) left right,
      candidate (X coordinate * left) right =
        candidate left (annihilator D coordinate right)) :
    candidate = fockForm D := by
  apply LinearMap.ext
  intro left
  apply LinearMap.ext
  intro right
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      simp [C_eq_smul_one, LinearMap.map_smulₛₗ, LinearMap.smul_apply, vacuum,
        fockForm_vacuum_left]
  | add first second first_induction second_induction =>
      simp [map_add, LinearMap.add_apply, first_induction, second_induction]
  | mul_X polynomial generator induction_hypothesis =>
      calc
        candidate (polynomial * X generator) right =
            candidate polynomial (annihilator D generator right) := by
          simpa only [mul_comm] using adjoint generator polynomial right
        _ = fockForm D polynomial (annihilator D generator right) := induction_hypothesis _
        _ = fockForm D (polynomial * X generator) right := by
          simpa only [neutralPolynomialMode_negative, neutralPolynomialMode_positive,
            LinearMap.mulLeft_apply, annihilator, mul_comm] using
            (fockForm_creation_adjoint D 0 generator.1 generator.2 polynomial right).symm

end

end D5.S3.VertexAlgebra.LatticeOscillatorFockForm
