/- GID: D5/S3/Observer/Monodromy/PrimitiveExteriorRecognition
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/PrimitiveExteriorRecognition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The actual primitive exterior action detects natural rank-one nilpotence without a rank assumption. -/

import D5.S3.Observer.Monodromy.ExteriorSquareContraction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Recognition from the primitive second exterior power

Skew coefficient matrices represent bivectors in characteristic different from
2. The primitive space is the actual kernel of B |-> trace(J B) within them.
For an invertible alternating J, J^-1 spans the invariant line, and the explicit
projection removes that line. The restricted endomorphism is constructed from
the genuine action B |-> X B + B X^t and its proved invariance.

If this restricted endomorphism squares to zero, the contraction theorem forces
X^2=0 and an outer-product factorization. Natural nilpotence, rank one, and an
invariant-line extension are conclusions of the calculation, not input fields.
In dimension eight the primitive space has dimension 27 by ordinary finite
linear algebra; that dimension count is not separately formalized here.
This does not construct an exterior lift for an arbitrary geometric local system.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.PrimitiveExteriorRecognition

open D5.S3.Observer.Monodromy.ExteriorSquareContraction

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- An actual subspace of bivector coefficient matrices cut out by contraction. -/
def primitiveSpace (J : Matrix I I K) : Submodule K (Matrix I I K) where
  carrier := {B | B.transpose = -B ∧ Matrix.trace (J * B) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro B C hB hC
    constructor
    · simp only [Matrix.transpose_add, hB.1, hC.1]
      abel
    · simp [Matrix.mul_add, Matrix.trace_add, hB.2, hC.2]
  smul_mem' := by
    intro c B hB
    constructor
    · simp [Matrix.transpose_smul, hB.1, smul_neg]
    · simp [Matrix.mul_smul, Matrix.trace_smul, hB.2]

private theorem action_skew (X B : Matrix I I K) (hB : B.transpose = -B) :
    (action X B).transpose = -action X B := by
  simp only [action_apply, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, hB, Matrix.neg_mul, Matrix.mul_neg]
  abel

private theorem action_contraction_zero (J X B : Matrix I I K)
    (hX : X.transpose * J = -(J * X)) : Matrix.trace (J * action X B) = 0 := by
  calc
    Matrix.trace (J * action X B) =
        Matrix.trace (J * X * B) + Matrix.trace (J * B * X.transpose) := by
      simp [action_apply, Matrix.mul_add, Matrix.trace_add, Matrix.mul_assoc]
    _ = Matrix.trace (J * X * B) + Matrix.trace (X.transpose * J * B) := by
      rw [Matrix.trace_mul_cycle J B X.transpose]
    _ = 0 := by rw [hX, Matrix.neg_mul, Matrix.trace_neg, add_neg_cancel]

/-- Invariance is proved from matrix multiplication and trace cyclicity. -/
theorem action_mem_primitive (J X : Matrix I I K)
    (hX : X.transpose * J = -(J * X)) {B : Matrix I I K}
    (hB : B ∈ primitiveSpace J) : action X B ∈ primitiveSpace J :=
  ⟨action_skew X B hB.1, action_contraction_zero J X B hX⟩

/-- The genuine restricted endomorphism, with the proved invariant subspace. -/
def primitiveAction (J X : Matrix I I K)
    (hX : X.transpose * J = -(J * X)) : Module.End K (primitiveSpace J) where
  toFun B := ⟨action X (B : Matrix I I K), action_mem_primitive J X hX B.property⟩
  map_add' B C := by
    apply Subtype.ext
    exact (action X).map_add _ _
  map_smul' c B := by
    apply Subtype.ext
    exact (action X).map_smul c _

private theorem inverse_skew (J : Matrix I I K)
    (hJ : J.transpose = -J) (hdet : J.det ≠ 0) :
    (J⁻¹).transpose = -J⁻¹ := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have hJI : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hneg : -((J⁻¹).transpose * J) = 1 := by
    have he := congrArg Matrix.transpose hJI
    simpa only [Matrix.transpose_mul, hJ, Matrix.mul_neg, Matrix.transpose_one] using he
  have hmul : (J⁻¹).transpose * J = -1 := neg_eq_iff_eq_neg.mp hneg
  calc
    (J⁻¹).transpose = ((J⁻¹).transpose * J) * J⁻¹ := by
      rw [Matrix.mul_assoc, hJI, Matrix.mul_one]
    _ = -J⁻¹ := by rw [hmul]; simp

/-- The missing invariant line is killed by the actual infinitesimal action. -/
theorem action_inverse_zero (J X : Matrix I I K) (hdet : J.det ≠ 0)
    (hX : X.transpose * J = -(J * X)) : action X J⁻¹ = 0 := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have hJI : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hIJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hq : J⁻¹ * X.transpose = -(X * J⁻¹) := by
    calc
      J⁻¹ * X.transpose = J⁻¹ * (X.transpose * J) * J⁻¹ := by
        simp only [Matrix.mul_assoc, hJI, Matrix.mul_one]
      _ = J⁻¹ * (-(J * X)) * J⁻¹ := by rw [hX]
      _ = -((J⁻¹ * J) * X * J⁻¹) := by noncomm_ring
      _ = -(X * J⁻¹) := by rw [hIJ]; simp
  rw [action_apply, hq, add_neg_cancel]

/-- Trace zero is derived from the skew-adjoint equation, not postulated. -/
theorem trace_zero_of_skewAdjoint (J X : Matrix I I K) (hdet : J.det ≠ 0)
    (hX : X.transpose * J = -(J * X)) (h2 : (2 : K) ≠ 0) :
    Matrix.trace X = 0 := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have hJI : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hIJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have ht : Matrix.trace X = -Matrix.trace X := by
    calc
      Matrix.trace X = Matrix.trace X.transpose := (Matrix.trace_transpose X).symm
      _ = Matrix.trace (X.transpose * (J * J⁻¹)) := by rw [hJI, Matrix.mul_one]
      _ = Matrix.trace ((X.transpose * J) * J⁻¹) := by rw [Matrix.mul_assoc]
      _ = -Matrix.trace (J * X * J⁻¹) := by rw [hX, Matrix.neg_mul, Matrix.trace_neg]
      _ = -Matrix.trace (J⁻¹ * J * X) := by rw [Matrix.trace_mul_cycle J X J⁻¹]
      _ = -Matrix.trace X := by rw [hIJ, Matrix.one_mul]
  have he : (2 : K) * Matrix.trace X = 0 := by linear_combination ht
  exact (mul_eq_zero.mp he).resolve_left h2

/-- The actual projector onto the contraction kernel, along the invariant line. -/
def project (J B : Matrix I I K) : Matrix I I K :=
  B - (Matrix.trace (J * B) / (Fintype.card I : K)) • J⁻¹

/-- Each projected bivector really lies in the primitive subspace. -/
theorem project_mem_primitive (J B : Matrix I I K)
    (hJ : J.transpose = -J) (hdet : J.det ≠ 0)
    (hn : (Fintype.card I : K) ≠ 0) (hB : B.transpose = -B) :
    project J B ∈ primitiveSpace J := by
  have hInv := inverse_skew J hJ hdet
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have htr : Matrix.trace (J * J⁻¹) = (Fintype.card I : K) := by
    rw [Matrix.mul_nonsing_inv J hu, Matrix.trace_one]
  constructor
  · simp only [project, Matrix.transpose_sub, Matrix.transpose_smul, hB, hInv, smul_neg]
    abel
  · simp only [project, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, htr]
    rw [div_mul_cancel₀ _ hn, sub_self]

/-- Removing the invariant line loses no infinitesimal action. -/
theorem action_project (J X B : Matrix I I K) (hdet : J.det ≠ 0)
    (hX : X.transpose * J = -(J * X)) : action X (project J B) = action X B := by
  rw [project, map_sub, map_smul, action_inverse_zero J X hdet hX, smul_zero, sub_zero]

/-- A direct recovery formula using only primitive inputs. In dimension eight
and characteristic zero its nonzero scalar is exactly six. -/
theorem primitive_first_contraction (J X : Matrix I I K)
    (hdet : J.det ≠ 0) (hX : X.transpose * J = -(J * X))
    (h2 : (2 : K) ≠ 0) (i k : I) :
    (∑ j, action X (project J (wedgeUnit k j)) i j) =
      ((Fintype.card I : K) - 2) * X i k := by
  simp_rw [action_project J X _ hdet hX]
  rw [first_contraction, trace_zero_of_skewAdjoint J X hdet hX h2]
  simp

/-- The primitive zero-square condition is transported to actual bivector units;
this is the substantive invariant-line step, not an assumed extension. -/
theorem primitive_square_zero_on_wedges (J X : Matrix I I K)
    (hJ : J.transpose = -J) (hdet : J.det ≠ 0)
    (hn : (Fintype.card I : K) ≠ 0)
    (hX : X.transpose * J = -(J * X))
    (hquad : (primitiveAction J X hX) ^ 2 = 0) :
    ∀ k l, action X (action X (wedgeUnit k l)) = 0 := by
  intro k l
  let B : primitiveSpace J :=
    ⟨project J (wedgeUnit k l),
      project_mem_primitive J (wedgeUnit k l) hJ hdet hn (wedgeUnit_skew k l)⟩
  have hv := congrArg (fun f : Module.End K (primitiveSpace J) => f B) hquad
  simp only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] at hv
  have hm := congrArg (fun y : primitiveSpace J => (y : Matrix I I K)) hv
  change action X (action X (project J (wedgeUnit k l))) = 0 at hm
  rw [action_project J X _ hdet hX] at hm
  exact hm

/-- Complete natural rank-one recognition from the square of the actual
primitive exterior endomorphism. The natural operator need not be supplied
as nilpotent or rank one; both properties are forced by the primitive data. -/
theorem primitive_square_zero_rank_one (J X : Matrix I I K)
    (hJ : J.transpose = -J) (hdet : J.det ≠ 0)
    (hX : X.transpose * J = -(J * X))
    (h2 : (2 : K) ≠ 0) (hn : (Fintype.card I : K) ≠ 0)
    (hn2 : (Fintype.card I : K) - 2 ≠ 0)
    (hn4 : (Fintype.card I : K) - 4 ≠ 0)
    (hquad : (primitiveAction J X hX) ^ 2 = 0) :
    X * X = 0 ∧ ∃ u v : I → K,
      (∀ i j, X i j = u i * v j) ∧ (∑ j, v j * u j) = 0 := by
  exact exterior_square_zero_rank_one X
    (trace_zero_of_skewAdjoint J X hdet hX h2) h2 hn2 hn4
    (primitive_square_zero_on_wedges J X hJ hdet hn hX hquad)

/-- The dimension-eight specialization relevant to the primitive 27-dimensional
representation. The general scalar restrictions are discharged, not retained. -/
theorem dimension_eight_recognition [CharZero K]
    (J X : Matrix (Fin 8) (Fin 8) K)
    (hJ : J.transpose = -J) (hdet : J.det ≠ 0)
    (hX : X.transpose * J = -(J * X))
    (hquad : (primitiveAction J X hX) ^ 2 = 0) :
    X * X = 0 ∧ ∃ u v : Fin 8 → K,
      (∀ i j, X i j = u i * v j) ∧ (∑ j, v j * u j) = 0 := by
  exact primitive_square_zero_rank_one J X hJ hdet hX
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hquad

#print axioms primitive_first_contraction
#print axioms primitive_square_zero_rank_one
#print axioms dimension_eight_recognition

end D5.S3.Observer.Monodromy.PrimitiveExteriorRecognition
