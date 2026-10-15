/- GID: D5/S3/VertexAlgebra/LatticeOscillatorFockMetric
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeOscillatorFockMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Algebraic nondegeneracy and positive Gram metric on the native oscillator. -/

/-
admission_basis: escape-witness
escape_witness: inverse_annihilators and the radical degree induction in
fockForm_nondegenerate prove separation for every native polynomial.
The independently consumed factorial insertion and directional_substitution
prove the actual Gram-coordinate pairing, rather than posit an isometry.
proof_shape: fockForm_nondegenerate: content; utility: none.
proof_shape: fockForm_coordinate_factorization: content; utility: none;
consumed by fockForm_factor_norm and fockForm_orthogonal_monomials.
proof_shape: fockForm_norm_coefficients: content; utility: none;
consumed by fockForm_positive.
proof_shape: fockForm_positive: content; utility: none.
proof_shape: fockForm_orthogonal_monomials: content; utility: none.
Classification expands same-delivery helpers to the inherited form and pinned
Mathlib suppliers. Each private helper is consumed in these proof paths.
All standard Fock mathematics, LDL and linear transport have zero novelty.
Both inverse Gram equations remain explicit; degree descent uses H G = 1.
-/

import D5.S3.VertexAlgebra.LatticeOscillatorFockForm
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOscillatorFockMetric

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeOscillatorFockForm
open MvPolynomial
open Matrix
open scoped BigOperators Matrix

noncomputable section

private theorem inverse_annihilators (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (coordinate : Index D) (polynomial : Oscillator D) :
    (∑ axis : Fin D.rank, (H coordinate.1 axis / (coordinate.2 + 1 : ℂ)) •
      annihilator D (axis, coordinate.2) polynomial) = pderiv coordinate polynomial := by
  classical
  simp only [annihilator, weightedPartial, LinearMap.smul_apply, LinearMap.sum_apply,
    Derivation.coeFn_coe, smul_smul]
  have frequency_ne : (coordinate.2 + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero coordinate.2
  simp only [div_mul_cancel₀ _ frequency_ne, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have inverse : ∀ axis, (∑ other, H coordinate.1 other * (D.G other axis : ℂ)) =
      if coordinate.1 = axis then 1 else 0 := by
    intro axis
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply] using
      congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ =>
        matrix coordinate.1 axis) hHG
  simp [inverse]

theorem fockForm_nondegenerate (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (fockForm D).Nondegenerate := by
  classical
  have left_separating : (fockForm D).SeparatingLeft := by
    intro polynomial
    induction degree : polynomial.totalDegree using Nat.strong_induction_on
        generalizing polynomial with
    | h degree induction_hypothesis =>
      intro radical
      have derivative_radical : ∀ coordinate : Index D, ∀ right,
          fockForm D (pderiv coordinate polynomial) right = 0 := by
        intro coordinate right
        rw [← inverse_annihilators D H hHG coordinate polynomial]
        simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
          LinearMap.smul_apply]
        apply Finset.sum_eq_zero
        intro axis _
        have adjoint := fockForm_annihilation_adjoint D 0 axis coordinate.2 polynomial right
        rw [neutralPolynomialMode_positive, neutralPolynomialMode_negative] at adjoint
        change fockForm D (annihilator D (axis, coordinate.2) polynomial) right = _ at adjoint
        rw [adjoint, radical, smul_zero]
      have derivatives_zero : ∀ coordinate : Index D, pderiv coordinate polynomial = 0 := by
        intro coordinate
        by_cases zero : pderiv coordinate polynomial = 0
        · exact zero
        have smaller : (pderiv coordinate polynomial).totalDegree < polynomial.totalDegree := by
          run_tac
            let supplier := (Lean.Name.num
              `_private.D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity 0).append
              `D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.totalDegree_pderiv_lt
            Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($(Lean.mkIdent supplier))))
          exact zero
        exact induction_hypothesis _ (degree ▸ smaller) _ rfl (derivative_radical coordinate)
      have constant : polynomial = C (constantCoeff polynomial) := by
        run_tac
          let supplier := (Lean.Name.num
            `_private.D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity 0).append
            `D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.eq_constant_of_partials_zero
          Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($(Lean.mkIdent supplier))))
        exact derivatives_zero
      have coefficient_zero : constantCoeff polynomial = 0 := by
        have symmetry := (fockForm_isSymm D).eq polynomial 1
        rw [radical, map_zero, fockForm_vacuum_left] at symmetry
        exact symmetry.symm
      rw [constant, coefficient_zero, map_zero]
  refine ⟨left_separating, ?_⟩
  intro polynomial radical
  apply left_separating polynomial
  intro right
  have symmetry := (fockForm_isSymm D).eq right polynomial
  rw [radical, map_zero] at symmetry
  exact symmetry.symm

def occupationWeight (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (occupation : Index D →₀ ℕ) : ℝ :=
  occupation.prod (fun coordinate count =>
    (count.factorial : ℝ) * ((coordinate.2 + 1 : ℝ) * diagonal coordinate.1) ^ count)

private theorem occupationWeight_insert (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (occupation : Index D →₀ ℕ) (coordinate : Index D) :
    occupationWeight D diagonal (occupation + Finsupp.single coordinate 1) =
      (occupation coordinate + 1 : ℝ) * ((coordinate.2 + 1 : ℝ) * diagonal coordinate.1) *
        occupationWeight D diagonal occupation := by
  classical
  let factor : Index D → ℕ → ℝ := fun index count =>
    (count.factorial : ℝ) * ((index.2 + 1 : ℝ) * diagonal index.1) ^ count
  have factor_zero : ∀ index, factor index 0 = 1 := by intro index; simp [factor]
  have erased : (occupation + Finsupp.single coordinate 1).erase coordinate =
      occupation.erase coordinate := by
    ext index
    by_cases equal : index = coordinate <;> simp [equal]
  change (occupation + Finsupp.single coordinate 1).prod factor =
    _ * _ * occupation.prod factor
  rw [← Finsupp.mul_prod_erase' _ coordinate factor factor_zero, erased,
    ← Finsupp.mul_prod_erase' occupation coordinate factor factor_zero]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, factor, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

private def diagonalBilinear (D : LatticeData) (diagonal : Fin D.rank → ℝ) :
    Oscillator D →ₗ[ℂ] Oscillator D →ₗ[ℂ] ℂ :=
  (basisMonomials (Index D) ℂ).constr ℂ (fun occupation =>
    (occupationWeight D diagonal occupation : ℂ) • lcoeff ℂ occupation)

private def diagonalForm (D : LatticeData) (diagonal : Fin D.rank → ℝ) :
    Oscillator D →ₗ⋆[ℂ] Oscillator D →ₗ[ℂ] ℂ :=
  (diagonalBilinear D diagonal).comp (conjugatePolynomial D)

private theorem diagonalForm_monomial (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (occupation : Index D →₀ ℕ) (scalar : ℂ) (polynomial : Oscillator D) :
    diagonalForm D diagonal (monomial occupation scalar) polynomial =
      star scalar * (occupationWeight D diagonal occupation : ℂ) * coeff occupation polynomial := by
  have monomial_scalar : (monomial occupation (star scalar) : Oscillator D) =
      star scalar • monomial occupation 1 := by simp [smul_monomial]
  change diagonalBilinear D diagonal
    (MvPolynomial.map (starRingEnd ℂ) (monomial occupation scalar)) polynomial = _
  rw [map_monomial]
  change diagonalBilinear D diagonal (monomial occupation (star scalar)) polynomial = _
  rw [monomial_scalar, map_smul, LinearMap.smul_apply]
  have basis_value := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => (occupationWeight D diagonal exponent : ℂ) • lcoeff ℂ exponent) occupation
  change diagonalBilinear D diagonal (monomial occupation 1) = _ at basis_value
  rw [basis_value]
  simp [smul_eq_mul, mul_assoc]

private theorem diagonalForm_creator (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (coordinate : Index D) (left right : Oscillator D) :
    diagonalForm D diagonal (X coordinate * left) right =
      diagonalForm D diagonal left
        (((coordinate.2 + 1 : ℂ) * (diagonal coordinate.1 : ℂ)) • pderiv coordinate right) := by
  classical
  induction left using MvPolynomial.induction_on' with
  | add first second first_induction second_induction =>
      simp [mul_add, map_add, LinearMap.add_apply, first_induction, second_induction]
  | monomial occupation scalar =>
      have insertion : X coordinate * (monomial occupation scalar : Oscillator D) =
          monomial (occupation + Finsupp.single coordinate 1) scalar := by
        simpa [mul_comm] using
          (monomial_add_single (s := occupation) (n := coordinate) (e := 1) (a := scalar)).symm
      rw [insertion, diagonalForm_monomial, diagonalForm_monomial, occupationWeight_insert]
      simp only [coeff_smul, coeff_pderiv, Complex.real_smul, smul_eq_mul,
        Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
      ring

private theorem diagonalForm_vacuum (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (polynomial : Oscillator D) :
    diagonalForm D diagonal 1 polynomial = constantCoeff polynomial := by
  rw [one_def, diagonalForm_monomial]
  simp [occupationWeight, constantCoeff_eq]

private theorem diagonalForm_coefficients (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (left right : Oscillator D) :
    diagonalForm D diagonal left right = ∑ occupation ∈ left.support,
      star (coeff occupation left) * (occupationWeight D diagonal occupation : ℂ) *
        coeff occupation right := by
  conv_lhs => rw [left.as_sum]
  simp only [map_sum, LinearMap.sum_apply, diagonalForm_monomial]

private theorem diagonalForm_norm (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (polynomial : Oscillator D) :
    diagonalForm D diagonal polynomial polynomial = (∑ occupation ∈ polynomial.support,
      occupationWeight D diagonal occupation *
        Complex.normSq (coeff occupation polynomial) : ℝ) := by
  rw [diagonalForm_coefficients]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro occupation _
  rw [mul_comm (star _), mul_assoc]
  change (occupationWeight D diagonal occupation : ℂ) *
    ((starRingEnd ℂ) (coeff occupation polynomial) * coeff occupation polynomial) = _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

def coordinateSubstitution (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℝ) :
    Oscillator D →ₐ[ℂ] Oscillator D :=
  aeval (fun coordinate : Index D =>
    ∑ axis : Fin D.rank, (frame coordinate.1 axis : ℂ) • X (axis, coordinate.2))

private theorem coordinateSubstitution_constantCoeff (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℝ) (polynomial : Oscillator D) :
    constantCoeff (coordinateSubstitution D frame polynomial) = constantCoeff polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [coordinateSubstitution]
  | add first second first_induction second_induction =>
      simp [map_add, first_induction, second_induction]
  | mul_X polynomial coordinate induction_hypothesis =>
      simp [coordinateSubstitution, map_sum, constantCoeff_smul]

private def directional (D : LatticeData) (vector : Fin D.rank → ℝ) (frequency : ℕ) :
    Module.End ℂ (Oscillator D) :=
  ∑ axis : Fin D.rank, (vector axis : ℂ) • (pderiv (axis, frequency)).toLinearMap

private theorem directional_mul (D : LatticeData) (vector : Fin D.rank → ℝ)
    (frequency : ℕ) (left right : Oscillator D) :
    directional D vector frequency (left * right) =
      directional D vector frequency left * right +
        left * directional D vector frequency right := by
  simp [directional, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    pderiv_mul, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, mul_comm, add_comm]

private theorem directional_X (D : LatticeData) (vector : Fin D.rank → ℝ)
    (frequency : ℕ) (coordinate : Index D) :
    directional D vector frequency (X coordinate) =
      if frequency = coordinate.2 then C (vector coordinate.1 : ℂ) else 0 := by
  classical
  rcases coordinate with ⟨axis, actual_frequency⟩
  by_cases equal : frequency = actual_frequency
  · subst actual_frequency
    simp [directional, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
      pderiv_X, Pi.single_apply, Prod.mk.injEq, C_eq_smul_one]
  · simp [directional, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
      pderiv_X, Pi.single_apply, Prod.mk.injEq, equal, Ne.symm equal, C_eq_smul_one]

private theorem directional_substitution (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℝ) (vector : Fin D.rank → ℝ)
    (frequency : ℕ) (polynomial : Oscillator D) :
    directional D vector frequency (coordinateSubstitution D frame polynomial) =
      coordinateSubstitution D frame (directional D (frame *ᵥ vector) frequency polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [coordinateSubstitution, directional, LinearMap.sum_apply,
      LinearMap.smul_apply, Derivation.coeFn_coe]
  | add first second first_induction second_induction =>
      simp [map_add, first_induction, second_induction]
  | mul_X polynomial coordinate induction_hypothesis =>
      rw [map_mul, directional_mul, induction_hypothesis, directional_mul, map_add, map_mul,
        map_mul]
      congr 1
      congr 1
      simp only [coordinateSubstitution, aeval_X, map_sum, map_smul, directional_X,
        Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
      split_ifs <;> simp [Finset.sum_mul, MvPolynomial.smul_eq_C_mul, map_sum]

private theorem coordinateSubstitution_comp (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℝ) :
    (coordinateSubstitution D frame).comp (coordinateSubstitution D inverse) =
      coordinateSubstitution D (inverse * frame) := by
  classical
  apply MvPolynomial.algHom_ext
  intro coordinate
  simp only [AlgHom.comp_apply, coordinateSubstitution, aeval_X, map_sum, map_smul,
    Finset.smul_sum, smul_smul, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro axis _
  rw [Finset.sum_smul]

private theorem coordinateSubstitution_one (D : LatticeData) :
    coordinateSubstitution D (1 : Matrix (Fin D.rank) (Fin D.rank) ℝ) = AlgHom.id ℂ _ := by
  classical
  apply MvPolynomial.algHom_ext
  intro coordinate
  simp [coordinateSubstitution, Matrix.one_apply]

def coordinateEquiv (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℝ)
    (left_inverse : inverse * frame = 1) (right_inverse : frame * inverse = 1) :
    Oscillator D ≃ₐ[ℂ] Oscillator D :=
  AlgEquiv.ofAlgHom (coordinateSubstitution D frame) (coordinateSubstitution D inverse)
    (by rw [coordinateSubstitution_comp, left_inverse, coordinateSubstitution_one])
    (by rw [coordinateSubstitution_comp, right_inverse, coordinateSubstitution_one])

private theorem annihilator_substitution (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℝ) (diagonal : Fin D.rank → ℝ)
    (factorization : (fun axis other => (D.G axis other : ℝ)) =
      frame * Matrix.diagonal diagonal * frame.transpose)
    (coordinate : Index D) (polynomial : Oscillator D) :
    coordinateSubstitution D frame (annihilator D coordinate polynomial) =
      ∑ axis : Fin D.rank, (frame coordinate.1 axis : ℂ) •
        (((coordinate.2 + 1 : ℂ) * (diagonal axis : ℂ)) •
          pderiv (axis, coordinate.2) (coordinateSubstitution D frame polynomial)) := by
  classical
  let vector : Fin D.rank → ℝ := fun axis => frame coordinate.1 axis * diagonal axis
  have row : frame *ᵥ vector = fun axis => (D.G coordinate.1 axis : ℝ) := by
    funext axis
    have identity := congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℝ =>
      matrix coordinate.1 axis) factorization
    rw [Matrix.mul_apply] at identity
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at identity
    simp only [Matrix.mulVec, dotProduct, vector]
    rw [identity]
    apply Finset.sum_congr rfl
    intro other _
    ring
  have chain := directional_substitution D frame vector coordinate.2 polynomial
  rw [row] at chain
  have native : annihilator D coordinate polynomial =
      (coordinate.2 + 1 : ℂ) •
        directional D (fun axis => (D.G coordinate.1 axis : ℝ)) coordinate.2 polynomial := by
    simp [annihilator, weightedPartial, directional, LinearMap.sum_apply,
      LinearMap.smul_apply, Derivation.coeFn_coe]
  rw [native, map_smul, ← chain]
  simp only [directional, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    Finset.smul_sum, vector, Complex.ofReal_mul, smul_smul]
  apply Finset.sum_congr rfl
  intro axis _
  congr 1
  ring

theorem fockForm_coordinate_factorization (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℝ) (diagonal : Fin D.rank → ℝ)
    (factorization : (fun axis other => (D.G axis other : ℝ)) =
      frame * Matrix.diagonal diagonal * frame.transpose)
    (left right : Oscillator D) :
    fockForm D left right =
      ∑ occupation ∈ (coordinateSubstitution D frame left).support,
        star (coeff occupation (coordinateSubstitution D frame left)) *
          (occupationWeight D diagonal occupation : ℂ) *
            coeff occupation (coordinateSubstitution D frame right) := by
  classical
  let candidate : Oscillator D →ₗ⋆[ℂ] Oscillator D →ₗ[ℂ] ℂ :=
    (LinearMap.compl₂ (diagonalForm D diagonal)
      (coordinateSubstitution D frame).toLinearMap).comp
        (coordinateSubstitution D frame).toLinearMap
  have vacuum : ∀ polynomial, candidate 1 polynomial = constantCoeff polynomial := by
    intro polynomial
    change diagonalForm D diagonal (coordinateSubstitution D frame 1)
      (coordinateSubstitution D frame polynomial) = _
    rw [map_one, diagonalForm_vacuum, coordinateSubstitution_constantCoeff]
  have adjoint : ∀ (coordinate : Index D) left right,
      candidate (X coordinate * left) right = candidate left (annihilator D coordinate right) := by
    intro coordinate left right
    change diagonalForm D diagonal (coordinateSubstitution D frame (X coordinate * left))
      (coordinateSubstitution D frame right) =
        diagonalForm D diagonal (coordinateSubstitution D frame left)
          (coordinateSubstitution D frame (annihilator D coordinate right))
    rw [map_mul]
    have generator : coordinateSubstitution D frame (X coordinate) =
        ∑ axis : Fin D.rank, (frame coordinate.1 axis : ℂ) • X (axis, coordinate.2) := by
      simp [coordinateSubstitution]
    rw [generator, Finset.sum_mul, annihilator_substitution D frame diagonal factorization]
    simp only [smul_mul_assoc, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro axis _
    rw [show (starRingEnd ℂ) (frame coordinate.1 axis : ℂ) =
      (frame coordinate.1 axis : ℂ) by simp]
    rw [diagonalForm_creator]
    simp only [map_smul, RingHom.id_apply, Prod.fst, Prod.snd]
  have equality := fockForm_unique D candidate vacuum adjoint
  rw [← diagonalForm_coefficients]
  exact congrArg (fun form => form left right) equality.symm

private theorem fockForm_factor_norm (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℝ) (diagonal : Fin D.rank → ℝ)
    (factorization : (fun axis other => (D.G axis other : ℝ)) =
      frame * Matrix.diagonal diagonal * frame.transpose)
    (polynomial : Oscillator D) :
    fockForm D polynomial polynomial =
      (∑ occupation ∈ (coordinateSubstitution D frame polynomial).support,
        occupationWeight D diagonal occupation *
          Complex.normSq (coeff occupation (coordinateSubstitution D frame polynomial)) : ℝ) := by
  rw [fockForm_coordinate_factorization D frame diagonal factorization,
    ← diagonalForm_coefficients, diagonalForm_norm]

private theorem occupationWeight_pos (D : LatticeData) (diagonal : Fin D.rank → ℝ)
    (positive : ∀ axis, 0 < diagonal axis) (occupation : Index D →₀ ℕ) :
    0 < occupationWeight D diagonal occupation := by
  classical
  apply Finset.prod_pos
  intro coordinate _
  apply mul_pos
  · exact_mod_cast Nat.factorial_pos (occupation coordinate)
  · exact pow_pos (mul_pos (by positivity) (positive coordinate.1)) _

def gramReal (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  fun axis other => (D.G axis other : ℝ)

private theorem ldl_factorization (D : LatticeData) (positive : (gramReal D).PosDef) :
    gramReal D = LDL.lower positive * Matrix.diagonal (LDL.diagEntries positive) *
      (LDL.lower positive).transpose := by
  simpa only [LDL.diag, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (LDL.lower_conj_diag positive).symm

private theorem ldl_positive (D : LatticeData) (positive : (gramReal D).PosDef) :
    ∀ axis, 0 < LDL.diagEntries positive axis := by
  have conjugate : (LDL.diag positive).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact (isUnit_of_invertible (LDL.lowerInv positive)).posDef_star_right_conjugate_iff.mpr
      positive
  intro axis
  simpa only [LDL.diag, Matrix.diagonal_apply_eq] using conjugate.diag_pos (i := axis)

theorem fockForm_norm_coefficients (D : LatticeData) (positive : (gramReal D).PosDef)
    (polynomial : Oscillator D) :
    fockForm D polynomial polynomial =
      (∑ occupation ∈ (coordinateSubstitution D (LDL.lower positive) polynomial).support,
        occupationWeight D (LDL.diagEntries positive) occupation * Complex.normSq
          (coeff occupation (coordinateSubstitution D (LDL.lower positive) polynomial)) : ℝ) := by
  exact fockForm_factor_norm D _ _ (ldl_factorization D positive) polynomial

theorem fockForm_positive (D : LatticeData) (positive : (gramReal D).PosDef)
    (polynomial : Oscillator D) (nonzero : polynomial ≠ 0) :
    0 < (fockForm D polynomial polynomial).re := by
  classical
  rw [fockForm_norm_coefficients D positive]
  rw [Complex.ofReal_re]
  have lower_right : LDL.lower positive * LDL.lowerInv positive = 1 :=
    Matrix.inv_mul_of_invertible _
  have lower_left : LDL.lowerInv positive * LDL.lower positive = 1 :=
    Matrix.mul_inv_of_invertible _
  let equivalence := coordinateEquiv D (LDL.lower positive) (LDL.lowerInv positive)
    lower_left lower_right
  have transformed_nonzero : coordinateSubstitution D (LDL.lower positive) polynomial ≠ 0 := by
    change equivalence polynomial ≠ 0
    exact equivalence.map_ne_zero_iff.mpr nonzero
  have support_nonempty := MvPolynomial.support_nonempty.mpr transformed_nonzero
  apply Finset.sum_pos
  · intro occupation member
    exact mul_pos (occupationWeight_pos D _ (ldl_positive D positive) occupation)
      (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp member))
  · exact support_nonempty

theorem fockForm_orthogonal_monomials (D : LatticeData) (positive : (gramReal D).PosDef)
    (left right : Index D →₀ ℕ) :
    fockForm D (coordinateSubstitution D (LDL.lowerInv positive) (monomial left 1))
      (coordinateSubstitution D (LDL.lowerInv positive) (monomial right 1)) =
      if left = right then (occupationWeight D (LDL.diagEntries positive) left : ℂ) else 0 := by
  classical
  have composition : (coordinateSubstitution D (LDL.lower positive)).comp
      (coordinateSubstitution D (LDL.lowerInv positive)) = AlgHom.id ℂ _ := by
    rw [coordinateSubstitution_comp, LDL.lower, Matrix.mul_inv_of_invertible,
      coordinateSubstitution_one]
  have inverse : ∀ polynomial : Oscillator D,
      coordinateSubstitution D (LDL.lower positive)
        (coordinateSubstitution D (LDL.lowerInv positive) polynomial) = polynomial := by
    intro polynomial
    exact congrArg (fun hom : Oscillator D →ₐ[ℂ] Oscillator D => hom polynomial) composition
  rw [fockForm_coordinate_factorization D _ _ (ldl_factorization D positive),
    inverse, inverse, ← diagonalForm_coefficients, diagonalForm_monomial]
  simp [coeff_monomial, eq_comm]

end

end D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
