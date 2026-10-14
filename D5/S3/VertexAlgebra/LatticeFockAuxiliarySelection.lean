/- GID: D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeFockAuxiliarySelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Auxiliary selection for the actual substituted oscillator Fock form. -/

/-
admission_basis: escape-witness
escape_witness: fockForm_auxiliary_selection uses actual creator contraction and
polynomial induction to prove auxiliary skewness for arbitrary finite occupation.
proof_shape: fockForm_auxiliary_selection: content
proof_shape: substituted_creator_adjoint: bind-only; consumed by auxiliary_skew
on the live proof path of fockForm_auxiliary_selection.
proof_shape: frame_hermitian_aux_balance: bind-only; consumed by
fockForm_auxiliary_selection. Its conjugation bridge is not a new abstract form.
All private helpers have actual proof consumers. This is a native structural
selection rule, not a claim of literature novelty or physical no-ghost positivity.
-/

import D5.S3.VertexAlgebra.LatticeOscillatorFockForm
import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary09

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeOscillatorFockForm OriginalQQuartetSource
open scoped BigOperators

noncomputable section

private theorem gramPair_star (D : LatticeData) (left right : Fin D.rank → ℂ) :
    gramPair D (fun axis => star (left axis)) (fun axis => star (right axis)) =
      star (gramPair D left right) := by
  simp [gramPair, star_sum, star_mul, mul_comm, mul_left_comm, mul_assoc]

theorem frame_hermitian_aux_balance (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (distinct : xAxis ≠ yAxis)
    (xReal : ∀ axis, star (frame xAxis axis) = frame xAxis axis)
    (yReal : ∀ axis, star (frame yAxis axis) = frame yAxis axis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (first second : Fin D.rank) :
    ((axisAuxDegree D xAxis yAxis first : ℂ) +
      (axisAuxDegree D xAxis yAxis second : ℂ)) *
      gramPair D (fun axis => star (frame first axis)) (frame second) = 0 := by
  apply balanced_axes D xAxis yAxis distinct
    (fun first second => gramPair D (fun axis => star (frame first axis)) (frame second))
  · intro row
    simpa only [xReal] using yDual row
  · intro row
    simpa only [yReal] using xDual row
  · intro row
    have conjugated := gramPair_star D (frame row) (frame xAxis)
    simp only [xReal] at conjugated
    rw [gramPair_symm D (frame row) (frame xAxis), yDual row] at conjugated
    by_cases equal : row = yAxis <;>
      simpa only [equal, if_true, if_false, star_one, star_zero] using conjugated
  · intro row
    have conjugated := gramPair_star D (frame row) (frame yAxis)
    simp only [yReal] at conjugated
    rw [gramPair_symm D (frame row) (frame yAxis), xDual row] at conjugated
    by_cases equal : row = xAxis <;>
      simpa only [equal, if_true, if_false, star_one, star_zero] using conjugated

theorem substituted_creator_adjoint (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (index : Index D)
    (left right : Oscillator D) :
    fockForm D (coordinateSub D frame (MvPolynomial.X index * left))
      (coordinateSub D frame right) =
    (index.2 + 1 : ℂ) * fockForm D (coordinateSub D frame left)
      (coordinateSub D frame (coordinateDerivative D frame
        (fun axis => star (frame index.1 axis)) index.2 right)) := by
  classical
  have creator (axis : Fin D.rank) :
      fockForm D (MvPolynomial.X (axis, index.2) * coordinateSub D frame left)
        (coordinateSub D frame right) =
      fockForm D (coordinateSub D frame left)
        (annihilator D (axis, index.2) (coordinateSub D frame right)) := by
    simpa only [neutralPolynomialMode_negative, LinearMap.mulLeft_apply,
      neutralPolynomialMode_positive, annihilator, LinearMap.smul_apply] using
      fockForm_creation_adjoint D 0 axis index.2
        (coordinateSub D frame left) (coordinateSub D frame right)
  calc
    _ = ∑ axis, star (frame index.1 axis) *
        fockForm D (coordinateSub D frame left)
          (annihilator D (axis, index.2) (coordinateSub D frame right)) := by
      simp only [map_mul, coordinateSub_X, coordinate, Finset.sum_mul,
        smul_mul_assoc, map_sum, map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, starRingEnd_apply,
        smul_eq_mul, creator]
    _ = fockForm D (coordinateSub D frame left)
        ((index.2 + 1 : ℂ) • originalDerivative D
          (fun axis => star (frame index.1 axis)) index.2
          (coordinateSub D frame right)) := by
      simp only [originalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.smul_sum, map_sum, map_smul, annihilator, smul_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro axis member
      ring
    _ = _ := by
      rw [original_derivative_coordinate_chain_rule]
      simp only [map_smul, smul_eq_mul]

private theorem coordinateSub_constantCoeff (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (polynomial : Oscillator D) :
    MvPolynomial.constantCoeff (coordinateSub D frame polynomial) =
      MvPolynomial.constantCoeff polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [coordinateSub]
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial index inductionHypothesis =>
      simp [map_mul, coordinateSub_X, coordinate, map_sum]

private theorem aux_constantCoeff (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (polynomial : Oscillator D) :
    MvPolynomial.constantCoeff (auxDiagonal D xAxis yAxis polynomial) = 0 := by
  change MvPolynomial.coeff 0 (auxDiagonal D xAxis yAxis polynomial) = 0
  simp [auxDiagonal_coeff]

private theorem derivative_aux_commutator (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (balance : ∀ first second,
      ((axisAuxDegree D xAxis yAxis first : ℂ) +
        (axisAuxDegree D xAxis yAxis second : ℂ)) *
        gramPair D (fun axis => star (frame first axis)) (frame second) = 0)
    (index : Index D) (polynomial : Oscillator D) :
    auxDiagonal D xAxis yAxis (coordinateDerivative D frame
      (fun axis => star (frame index.1 axis)) index.2 polynomial) -
      coordinateDerivative D frame (fun axis => star (frame index.1 axis)) index.2
        (auxDiagonal D xAxis yAxis polynomial) =
    (auxiliaryWeight D xAxis yAxis index : ℂ) • coordinateDerivative D frame
      (fun axis => star (frame index.1 axis)) index.2 polynomial := by
  classical
  simp only [coordinateDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub,
    smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro row member
  have scalarBalance := balance index.1 row
  have scalarEquality :
      gramPair D (fun axis => star (frame index.1 axis)) (frame row) *
        (-(auxiliaryWeight D xAxis yAxis (row, index.2) : ℂ)) =
      (auxiliaryWeight D xAxis yAxis index : ℂ) *
        gramPair D (fun axis => star (frame index.1 axis)) (frame row) := by
    simp only [auxiliaryWeight] at *
    linear_combination -scalarBalance
  change gramPair D (fun axis => star (frame index.1 axis)) (frame row) •
    (auxDiagonal D xAxis yAxis (MvPolynomial.pderiv (row, index.2) polynomial) -
      MvPolynomial.pderiv (row, index.2) (auxDiagonal D xAxis yAxis polynomial)) = _
  rw [auxDiagonal_pderiv, smul_smul, scalarEquality]
  rfl

private theorem auxiliary_skew (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (balance : ∀ first second,
      ((axisAuxDegree D xAxis yAxis first : ℂ) +
        (axisAuxDegree D xAxis yAxis second : ℂ)) *
        gramPair D (fun axis => star (frame first axis)) (frame second) = 0)
    (left right : Oscillator D) :
    fockForm D (coordinateSub D frame (auxDiagonal D xAxis yAxis left))
      (coordinateSub D frame right) +
    fockForm D (coordinateSub D frame left)
      (coordinateSub D frame (auxDiagonal D xAxis yAxis right)) = 0 := by
  classical
  induction left using MvPolynomial.induction_on generalizing right with
  | C scalar =>
      have fixed : auxDiagonal D xAxis yAxis (MvPolynomial.C scalar) = 0 := by
        simpa only [MvPolynomial.monomial_zero', map_zero, Int.cast_zero, zero_smul] using
          auxDiagonal_monomial D xAxis yAxis 0 scalar
      rw [fixed]
      have constant : MvPolynomial.C scalar = scalar • (1 : Oscillator D) := by
        simp [MvPolynomial.smul_eq_C_mul]
      simp only [map_zero, LinearMap.zero_apply, zero_add, constant, map_smul,
        map_one, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply,
        fockForm_vacuum_left, coordinateSub_constantCoeff, aux_constantCoeff,
        smul_zero]
  | add first second firstProof secondProof =>
      simp only [map_add, LinearMap.add_apply]
      linear_combination firstProof right + secondProof right
  | mul_X polynomial index inductionHypothesis =>
      rw [mul_comm polynomial (MvPolynomial.X index)]
      have creatorAux := auxDiagonal_multiply_X D xAxis yAxis index polynomial
      have creatorEquality :
          auxDiagonal D xAxis yAxis (MvPolynomial.X index * polynomial) =
          MvPolynomial.X index * auxDiagonal D xAxis yAxis polynomial +
            (auxiliaryWeight D xAxis yAxis index : ℂ) •
              (MvPolynomial.X index * polynomial) := by
        linear_combination creatorAux
      have derivativeEquality := derivative_aux_commutator D frame xAxis yAxis balance
        index right
      have derivativeRearranged :
          coordinateDerivative D frame (fun axis => star (frame index.1 axis)) index.2
            (auxDiagonal D xAxis yAxis right) =
          auxDiagonal D xAxis yAxis (coordinateDerivative D frame
            (fun axis => star (frame index.1 axis)) index.2 right) -
          (auxiliaryWeight D xAxis yAxis index : ℂ) • coordinateDerivative D frame
            (fun axis => star (frame index.1 axis)) index.2 right := by
        linear_combination -derivativeEquality
      rw [creatorEquality]
      simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply,
        LinearMap.smul_apply, starRingEnd_apply, star_intCast, smul_eq_mul,
        substituted_creator_adjoint]
      rw [derivativeRearranged]
      simp only [map_sub, map_smul, smul_eq_mul]
      linear_combination (index.2 + 1 : ℂ) * inductionHypothesis
        (coordinateDerivative D frame (fun axis => star (frame index.1 axis)) index.2 right)

theorem fockForm_auxiliary_selection (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (distinct : xAxis ≠ yAxis)
    (xReal : ∀ axis, star (frame xAxis axis) = frame xAxis axis)
    (yReal : ∀ axis, star (frame yAxis axis) = frame yAxis axis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (left right : Oscillator D) (leftDegree rightDegree : ℤ)
    (leftHomogeneous : MvPolynomial.IsWeightedHomogeneous
      (auxiliaryWeight D xAxis yAxis) left leftDegree)
    (rightHomogeneous : MvPolynomial.IsWeightedHomogeneous
      (auxiliaryWeight D xAxis yAxis) right rightDegree)
    (nonzero : leftDegree + rightDegree ≠ 0) :
    fockForm D (coordinateSub D frame left) (coordinateSub D frame right) = 0 := by
  have identity := auxiliary_skew D frame xAxis yAxis
    (frame_hermitian_aux_balance D frame xAxis yAxis distinct xReal yReal xDual yDual)
    left right
  rw [auxDiagonal_homogeneous D xAxis yAxis left leftDegree leftHomogeneous,
    auxDiagonal_homogeneous D xAxis yAxis right rightDegree rightHomogeneous] at identity
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply,
    star_intCast, smul_eq_mul, ← add_mul, ← Int.cast_add] at identity
  exact (mul_eq_zero.mp identity).resolve_left (Int.cast_ne_zero.mpr nonzero)

#print axioms frame_hermitian_aux_balance
#print axioms substituted_creator_adjoint
#print axioms fockForm_auxiliary_selection

end

end D5.S3.VertexAlgebra.LatticeFockAuxiliarySelection
