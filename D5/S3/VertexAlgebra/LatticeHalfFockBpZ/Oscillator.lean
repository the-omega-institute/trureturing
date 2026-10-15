/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Oscillator
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Oscillator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric complex-bilinear half-Fock pairing with native reflected current adjoints. -/

import D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeOscillatorFockForm LatticeOscillatorFockMetric MvPolynomial
open scoped BigOperators

noncomputable section

def modeScale (mode : ℕ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_eq_mul_self
    (-((mode : ℂ) + 1 / 2) / ((mode : ℂ) + 1)))

theorem modeScale_square (mode : ℕ) :
    modeScale mode * modeScale mode = -((mode : ℂ) + 1 / 2) / ((mode : ℂ) + 1) :=
  (Classical.choose_spec (IsAlgClosed.exists_eq_mul_self
    (-((mode : ℂ) + 1 / 2) / ((mode : ℂ) + 1)))).symm

theorem modeScale_ne_zero (mode : ℕ) : modeScale mode ≠ 0 := by
  have denominator : (mode : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < (mode : ℝ) + 1))
  have numerator : (mode : ℂ) + 1 / 2 ≠ 0 := by
    intro zero
    have realZero := congrArg Complex.re zero
    norm_num at realZero
    linarith [Nat.cast_nonneg (α := ℝ) mode]
  intro zero
  have equation := modeScale_square mode
  rw [zero, zero_mul] at equation
  exact (div_ne_zero (neg_ne_zero.mpr numerator) denominator) equation.symm

def scalePolynomial (D : LatticeData) (scalars : ℕ → ℂ) :
    Oscillator D →ₐ[ℂ] Oscillator D :=
  aeval (fun index : Index D => scalars index.2 • X index)

theorem scalePolynomial_C (D : LatticeData) (scalars : ℕ → ℂ) (scalar : ℂ) :
    scalePolynomial D scalars (C scalar) = C scalar := by
  simp [scalePolynomial]

theorem scalePolynomial_X (D : LatticeData) (scalars : ℕ → ℂ) (index : Index D) :
    scalePolynomial D scalars (X index) = scalars index.2 • X index := by
  simp [scalePolynomial]

theorem scalePolynomial_inverse (D : LatticeData) (scalars : ℕ → ℂ)
    (nonzero : ∀ mode, scalars mode ≠ 0) (polynomial : Oscillator D) :
    scalePolynomial D (fun mode => (scalars mode)⁻¹)
      (scalePolynomial D scalars polynomial) = polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp only [scalePolynomial_C]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionProof =>
    simp only [map_mul, scalePolynomial_X, map_smul, inductionProof, smul_smul,
      mul_inv_cancel₀ (nonzero index.2), one_smul]

def scaleEquiv (D : LatticeData) : Oscillator D ≃ₗ[ℂ] Oscillator D where
  toFun := scalePolynomial D modeScale
  invFun := scalePolynomial D (fun mode => (modeScale mode)⁻¹)
  left_inv := scalePolynomial_inverse D modeScale modeScale_ne_zero
  right_inv polynomial := by
    simpa only [inv_inv] using scalePolynomial_inverse D
      (fun mode => (modeScale mode)⁻¹) (fun mode => inv_ne_zero (modeScale_ne_zero mode))
      polynomial
  map_add' := map_add _
  map_smul' := map_smul _

private theorem integer_creator (D : LatticeData) (index : Index D)
    (first second : Oscillator D) :
    gramBilinear D (X index * first) second =
      gramBilinear D first (annihilator D index second) := by
  run_tac
    let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeOscillatorFockForm 0).append
      `D5.S3.VertexAlgebra.LatticeOscillatorFockForm.gramBilinear_creator_left
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _ _ _))

private theorem integer_annihilator_X (D : LatticeData) (first second : Index D)
    (polynomial : Oscillator D) :
    annihilator D first (X second * polynomial) =
      X second * annihilator D first polynomial + contraction D first second • polynomial := by
  run_tac
    let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeOscillatorFockForm 0).append
      `D5.S3.VertexAlgebra.LatticeOscillatorFockForm.annihilator_X_mul
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _ _ _))

theorem scaled_annihilator (D : LatticeData) (scalars : ℕ → ℂ)
    (index : Index D) (polynomial : Oscillator D) :
    annihilator D index (scalePolynomial D scalars polynomial) =
      scalars index.2 • scalePolynomial D scalars (annihilator D index polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    simp [scalePolynomial_C, annihilator, LatticeSugawaraCurrents.weightedPartial,
      LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof, smul_add]
  | mul_X polynomial generator inductionProof =>
    rw [mul_comm polynomial (X generator), map_mul, scalePolynomial_X]
    rw [Algebra.smul_mul_assoc, map_smul, integer_annihilator_X, inductionProof]
    rw [integer_annihilator_X, map_add, map_mul, scalePolynomial_X, map_smul]
    simp only [smul_add, smul_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    have balance : scalars generator.2 * contraction D index generator =
        scalars index.2 * contraction D index generator := by
      by_cases sameMode : index.2 = generator.2
      · simp only [sameMode]
      · simp [contraction, sameMode]
    rw [balance]
    rw [mul_comm (scalars generator.2) (scalars index.2)]

private theorem integer_nondegenerate (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * LatticeHalfFock.gramComplex D = 1)
    (rightInverse : LatticeHalfFock.gramComplex D * H = 1) :
    (gramBilinear D).Nondegenerate := by
  have involution : Function.Involutive (conjugatePolynomial D) := by
    intro polynomial
    run_tac
      let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeOscillatorFockForm 0).append
        `D5.S3.VertexAlgebra.LatticeOscillatorFockForm.conjugatePolynomial_involution
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _))
  have separation := fockForm_nondegenerate D H leftInverse rightInverse
  constructor
  · intro polynomial radical
    have zero : conjugatePolynomial D polynomial = 0 := by
      apply separation.1
      intro other
      change gramBilinear D (conjugatePolynomial D (conjugatePolynomial D polynomial)) other = 0
      rw [involution]
      exact radical other
    have equation := congrArg (conjugatePolynomial D) zero
    rw [involution polynomial, map_zero] at equation
    exact equation
  · intro polynomial radical
    apply separation.2
    intro other
    exact radical (conjugatePolynomial D other)

def oscillatorPairing (D : LatticeData) : LinearMap.BilinForm ℂ (Oscillator D) :=
  (gramBilinear D).compl₁₂ (scaleEquiv D).toLinearMap (scaleEquiv D).toLinearMap

theorem oscillator_pairing_apply (D : LatticeData) (first second : Oscillator D) :
    oscillatorPairing D first second =
      gramBilinear D (scaleEquiv D first) (scaleEquiv D second) := rfl

theorem oscillator_pairing_symm (D : LatticeData) : (oscillatorPairing D).IsSymm := by
  constructor
  intro first second
  rw [oscillator_pairing_apply, oscillator_pairing_apply]
  run_tac
    let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeOscillatorFockForm 0).append
      `D5.S3.VertexAlgebra.LatticeOscillatorFockForm.gramBilinear_symmetric
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _ _))

theorem oscillator_pairing_nondegenerate (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * LatticeHalfFock.gramComplex D = 1)
    (rightInverse : LatticeHalfFock.gramComplex D * H = 1) :
    (oscillatorPairing D).Nondegenerate := by
  have separation := integer_nondegenerate D H leftInverse rightInverse
  constructor
  · intro polynomial radical
    apply (scaleEquiv D).injective
    rw [map_zero]
    apply separation.1
    intro other
    simpa only [oscillator_pairing_apply, LinearEquiv.apply_symm_apply] using
      radical ((scaleEquiv D).symm other)
  · intro polynomial radical
    apply (scaleEquiv D).injective
    rw [map_zero]
    apply separation.2
    intro other
    simpa only [oscillator_pairing_apply, LinearEquiv.apply_symm_apply] using
      radical ((scaleEquiv D).symm other)

theorem oscillator_creator_adjoint (D : LatticeData) (index : Index D)
    (first second : Oscillator D) :
    oscillatorPairing D (X index * first) second =
      -oscillatorPairing D first
        (LatticeHalfFock.current D index.1 (index.2 : ℤ) second) := by
  have denominator : (index.2 : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < (index.2 : ℝ) + 1))
  rw [oscillator_pairing_apply]
  change gramBilinear D (scalePolynomial D modeScale (X index * first))
    (scalePolynomial D modeScale second) = _
  rw [map_mul, scalePolynomial_X, Algebra.smul_mul_assoc, map_smul,
    LinearMap.smul_apply, integer_creator, scaled_annihilator, map_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, modeScale_square]
  rw [oscillator_pairing_apply]
  change _ = -gramBilinear D (scalePolynomial D modeScale first)
    (scalePolynomial D modeScale (LatticeHalfFock.current D index.1 (index.2 : ℤ) second))
  simp only [LatticeHalfFock.current,
    if_neg (show ¬ (index.2 : ℤ) < 0 by omega),
    LatticeHalfFock.frequency, Int.cast_natCast, Int.toNat_natCast,
    LinearMap.smul_apply, map_smul, smul_eq_mul, annihilator,
    LatticeActualAnnihilation.annihilate]
  field_simp [denominator]
  <;> ring

theorem oscillator_current_adjoint (D : LatticeData) (axis : Fin D.rank) (mode : ℤ)
    (first second : Oscillator D) :
    oscillatorPairing D (LatticeHalfFock.current D axis mode first) second =
      -oscillatorPairing D first (LatticeHalfFock.current D axis (-mode - 1) second) := by
  by_cases negative : mode < 0
  · have reflected : -mode - 1 = (((-mode - 1).toNat : ℕ) : ℤ) := by
      omega
    rw [LatticeHalfFock.current, if_pos negative, LinearMap.mulLeft_apply, reflected]
    exact oscillator_creator_adjoint D (axis, (-mode - 1).toNat) first second
  · have positiveMode : mode = (mode.toNat : ℤ) := by omega
    have equation := oscillator_creator_adjoint D (axis, mode.toNat) second first
    rw [← positiveMode,
      (oscillator_pairing_symm D).eq (X (axis, mode.toNat) * second) first,
      (oscillator_pairing_symm D).eq second (LatticeHalfFock.current D axis mode first)]
      at equation
    have reflected : LatticeHalfFock.current D axis (-mode - 1) =
        LinearMap.mulLeft ℂ (X (axis, mode.toNat)) := by
      conv_lhs => rw [positiveMode, LatticeHalfFock.current_negative]
    rw [reflected, LinearMap.mulLeft_apply]
    linear_combination equation

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
