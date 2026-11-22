/- GID: D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive half-frequency form on the original oscillator carrier. -/

import D5.S3.VertexAlgebra.Lattice.Oscillator.LatticeOscillatorFockMetric
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockHermitian

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFock LatticeOscillatorFockForm
open MvPolynomial
open scoped BigOperators

noncomputable section

def scaleReal (mode : ℕ) : ℝ := Real.sqrt (((mode : ℝ) + 1 / 2) / (mode + 1))

def scaleFactor (mode : ℕ) : ℂ := scaleReal mode

theorem scaleReal_pos (mode : ℕ) : 0 < scaleReal mode := by
  apply Real.sqrt_pos.2
  positivity

theorem scaleFactor_ne_zero (mode : ℕ) : scaleFactor mode ≠ 0 := by
  unfold scaleFactor
  exact_mod_cast (ne_of_gt (scaleReal_pos mode))

theorem scaleFactor_balance (mode : ℕ) :
    scaleFactor mode * scaleFactor mode * (mode + 1) = (mode : ℂ) + 1 / 2 := by
  have real_identity : scaleReal mode * scaleReal mode * (mode + 1) =
      (mode : ℝ) + 1 / 2 := by
    rw [← pow_two, scaleReal, Real.sq_sqrt (by positivity)]
    exact div_mul_cancel₀ _ (by positivity)
  unfold scaleFactor
  have cast_identity := congrArg (fun value : ℝ => (value : ℂ)) real_identity
  push_cast at cast_identity
  exact cast_identity

def scaling (D : LatticeData) : Oscillator D →ₐ[ℂ] Oscillator D :=
  aeval (fun coordinate : Index D => scaleFactor coordinate.2 • X coordinate)

def inverseScaling (D : LatticeData) : Oscillator D →ₐ[ℂ] Oscillator D :=
  aeval (fun coordinate : Index D => (scaleFactor coordinate.2)⁻¹ • X coordinate)

theorem inverseScaling_scaling (D : LatticeData) (polynomial : Oscillator D) :
    inverseScaling D (scaling D polynomial) = polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [scaling, inverseScaling]
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial coordinate induction_hypothesis =>
    rw [map_mul, map_mul, induction_hypothesis]
    simp [scaling, inverseScaling, smul_smul, scaleFactor_ne_zero]

theorem scaling_inverseScaling (D : LatticeData) (polynomial : Oscillator D) :
    scaling D (inverseScaling D polynomial) = polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [scaling, inverseScaling]
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial coordinate induction_hypothesis =>
    rw [map_mul, map_mul, induction_hypothesis]
    simp [scaling, inverseScaling, smul_smul, scaleFactor_ne_zero]

theorem scaling_injective (D : LatticeData) : Function.Injective (scaling D) :=
  Function.LeftInverse.injective (inverseScaling_scaling D)

theorem pderiv_scaling (D : LatticeData) (coordinate : Index D)
    (polynomial : Oscillator D) :
    pderiv coordinate (scaling D polynomial) =
      scaleFactor coordinate.2 • scaling D (pderiv coordinate polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [scaling]
  | add first second firstProof secondProof => simp [map_add, smul_add, firstProof, secondProof]
  | mul_X polynomial generator induction_hypothesis =>
    have generator_image : scaling D (X generator) = scaleFactor generator.2 • X generator := by
      simp [scaling]
    simp only [map_mul, generator_image, pderiv_mul, map_add, map_smul,
      induction_hypothesis]
    by_cases equal : coordinate = generator
    · subst generator
      simp [pderiv_X, generator_image, smul_add,
        smul_mul_assoc, mul_smul_comm, smul_smul]
    · simp [pderiv_X, equal, Ne.symm equal,
        smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem annihilate_scaling (D : LatticeData) (axis : Fin D.rank) (mode : ℕ)
    (polynomial : Oscillator D) :
    LatticeActualAnnihilation.annihilate D axis mode (scaling D polynomial) =
      scaleFactor mode • scaling D (LatticeActualAnnihilation.annihilate D axis mode polynomial) := by
  simp only [LatticeActualAnnihilation.annihilate, LatticeSugawaraCurrents.weightedPartial,
    LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe, pderiv_scaling,
    map_sum, map_smul, Finset.smul_sum, smul_smul]
  congr 1
  funext other
  rw [mul_comm]

theorem scaling_current_positive (D : LatticeData) (axis : Fin D.rank) (mode : ℕ)
    (polynomial : Oscillator D) :
    scaling D (current D axis mode polynomial) =
      scaleFactor mode • annihilator D (axis, mode) (scaling D polynomial) := by
  simp only [current, show ¬ (mode : ℤ) < 0 by omega, if_false, Int.toNat_natCast,
    LinearMap.smul_apply, map_smul, annihilator, LinearMap.smul_apply,
    LatticeActualAnnihilation.annihilate]
  rw [← LatticeActualAnnihilation.annihilate, annihilate_scaling]
  simp only [smul_smul]
  congr 1
  simpa only [frequency, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
    mul_assoc, mul_left_comm, mul_comm] using
    (scaleFactor_balance mode).symm

def halfForm (D : LatticeData) : Oscillator D →ₗ⋆[ℂ] Oscillator D →ₗ[ℂ] ℂ :=
  { toFun := fun left => (fockForm D (scaling D left)).comp (scaling D).toLinearMap
    map_add' := by intro first second; ext right; simp
    map_smul' := by intro scalar left; ext right; simp }

theorem halfForm_apply (D : LatticeData) (left right : Oscillator D) :
    halfForm D left right = fockForm D (scaling D left) (scaling D right) := rfl

theorem halfForm_isSymm (D : LatticeData) : LinearMap.IsSymm (halfForm D) := by
  constructor
  intro left right
  exact (fockForm_isSymm D).eq (scaling D left) (scaling D right)

theorem halfForm_positive (D : LatticeData)
    (positive : (LatticeOscillatorFockMetric.gramReal D).PosDef)
    (polynomial : Oscillator D) (nonzero : polynomial ≠ 0) :
    0 < (halfForm D polynomial polynomial).re := by
  apply LatticeOscillatorFockMetric.fockForm_positive D positive
  exact fun equal => nonzero (scaling_injective D (equal.trans (map_zero _).symm))

theorem halfForm_nondegenerate (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1) :
    (halfForm D).Nondegenerate := by
  constructor
  · intro left radical
    have original : ∀ right, fockForm D (scaling D left) right = 0 := by
      intro right
      simpa only [halfForm_apply, scaling_inverseScaling] using radical (inverseScaling D right)
    have zero := (LatticeOscillatorFockMetric.fockForm_nondegenerate D matrixH hHG hGH).1
      (scaling D left) original
    exact scaling_injective D (zero.trans (map_zero _).symm)
  · intro right radical
    have original : ∀ left, fockForm D left (scaling D right) = 0 := by
      intro left
      simpa only [halfForm_apply, scaling_inverseScaling] using radical (inverseScaling D left)
    have zero := (LatticeOscillatorFockMetric.fockForm_nondegenerate D matrixH hHG hGH).2
      (scaling D right) original
    exact scaling_injective D (zero.trans (map_zero _).symm)

theorem halfForm_creation_adjoint (D : LatticeData) (axis : Fin D.rank) (mode : ℕ)
    (left right : Oscillator D) :
    halfForm D (current D axis (-(mode : ℤ) - 1) left) right =
      halfForm D left (current D axis mode right) := by
  rw [halfForm_apply, halfForm_apply, scaling_current_positive, current_negative]
  simp only [LinearMap.mulLeft_apply, scaling, map_mul, aeval_X, smul_mul_assoc]
  have original := fockForm_creation_adjoint D 0 axis mode (scaling D left) (scaling D right)
  rw [LatticeSugawaraCurrents.neutralPolynomialMode_negative,
    LatticeSugawaraCurrents.neutralPolynomialMode_positive] at original
  change fockForm D (scaleFactor mode • (X (axis, mode) * scaling D left))
    (scaling D right) = fockForm D (scaling D left)
      (scaleFactor mode • annihilator D (axis, mode) (scaling D right))
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul]
  rw [show starRingEnd ℂ (scaleFactor mode) = scaleFactor mode from Complex.conj_ofReal _]
  exact congrArg (fun value : ℂ => scaleFactor mode • value) original

theorem halfForm_current_adjoint (D : LatticeData) (axis : Fin D.rank) (mode : ℤ)
    (left right : Oscillator D) :
    halfForm D (current D axis mode left) right =
      halfForm D left (current D axis (-mode - 1) right) := by
  by_cases negative : mode < 0
  · obtain ⟨frequency, equality⟩ : ∃ frequency : ℕ, mode = -(frequency : ℤ) - 1 :=
      ⟨(-mode - 1).toNat, by omega⟩
    subst mode
    simpa using halfForm_creation_adjoint D axis frequency left right
  · obtain ⟨frequency, equality⟩ : ∃ frequency : ℕ, mode = frequency :=
      ⟨mode.toNat, by omega⟩
    subst mode
    have reverse := halfForm_creation_adjoint D axis frequency right left
    have starred := congrArg (starRingEnd ℂ) reverse
    rw [(halfForm_isSymm D).eq, (halfForm_isSymm D).eq] at starred
    exact starred.symm

end
end D5.S3.VertexAlgebra.LatticeHalfFockHermitian
