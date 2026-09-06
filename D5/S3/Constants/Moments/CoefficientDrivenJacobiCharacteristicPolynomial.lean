/- GID: D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict coefficient Hankel data give a positive Jacobi recurrence with charpoly q. -/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/- Library-search audit trail (2026-09-06):
   * Repository searches for `coefficient_driven_jacobi_characteristic_polynomial`,
     Hankel/Jacobi constructions, orthogonal polynomials, and tridiagonal characteristic
     polynomials found no exact declaration. `HankelJacobiDeterminant` only proves positivity
     of a determinant-defined candidate, `FiniteStieltjesOperatorRealization` only gives a
     diagonal finite-atomic realization, and `NewtonPowerSumCharacteristicPolynomial` starts
     from power sums already known to agree.
   * Pinned-Mathlib searches found the general primitives
     `InnerProductSpace.gramSchmidtBasis`, `gramSchmidt_orthogonal`,
     `gramSchmidt_triangular`, `PowerBasis.leftMulMatrix`, and
     `Algebra.charpoly_leftMulMatrix`. No result combines them into the coefficient-driven
     orthogonal-polynomial/Jacobi construction proved below.
   * Searches across the pinned non-Mathlib Lean dependencies (`batteries`, `aesop`, `Qq`,
     `Cli`, `LeanSearchClient`, `importGraph`, `plausible`, and `proofwidgets`) for
     orthogonal-polynomial, Jacobi-matrix, Hankel-charpoly, and three-term-recurrence variants
     returned no matches. An online GitHub code-search request through NyxID failed with HTTP
     400 because the available OAuth connection was `pending_auth`; no online result is claimed.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace
open Finset Module Polynomial Submodule

namespace D5.S3.Constants.Moments.CoefficientDrivenJacobiCharacteristicPolynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- The companion-shaped multiplication matrix determined by the coefficients of a monic
polynomial. -/
def coefficientMultiplicationMatrix (q : Real[X]) :
    Matrix (Fin q.natDegree) (Fin q.natDegree) Real :=
  fun i j =>
    if j.1 + 1 = q.natDegree then -q.coeff i.1 else if i.1 = j.1 + 1 then 1 else 0

/-- The coefficient-driven multiplication operator in a chosen power basis. -/
noncomputable def coefficientMultiplication (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E) : Module.End Real E :=
  Matrix.toLin power power (coefficientMultiplicationMatrix q)

/-- The Hankel pairing of two coefficient vectors for a prescribed moment sequence. -/
noncomputable def coefficientHankelValue {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E)
    (moment : Nat -> Real) (x y : E) : Real :=
  ∑ i, ∑ j, power.repr x i * power.repr y j * moment (i.1 + j.1)

/-- Strict positivity of the finite coefficient Hankel form. -/
def StrictPositiveHankel {q : Real[X]} (power : Basis (Fin q.natDegree) Real E)
    (moment : Nat -> Real) : Prop :=
  forall x : E, x ≠ 0 -> 0 < coefficientHankelValue power moment x x

private noncomputable def orthogonalPowerBasis {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E) : Basis (Fin q.natDegree) Real E :=
  InnerProductSpace.gramSchmidtBasis power

private noncomputable def jacobiMatrix (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E) :
    Matrix (Fin q.natDegree) (Fin q.natDegree) Real :=
  LinearMap.toMatrix (orthogonalPowerBasis power) (orthogonalPowerBasis power)
    (coefficientMultiplication q power)

private noncomputable def squaredNorm {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E) (i : Fin q.natDegree) : Real :=
  inner Real (orthogonalPowerBasis power i) (orthogonalPowerBasis power i)

private def previousIndex {q : Real[X]} (j : Fin q.natDegree) : Fin q.natDegree :=
  ⟨j.1 - 1, lt_of_le_of_lt (Nat.sub_le ..) j.isLt⟩

private theorem orthogonal_power_basis_apply {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E) (i : Fin q.natDegree) :
    orthogonalPowerBasis power i = InnerProductSpace.gramSchmidt Real power i := by
  exact congrFun (InnerProductSpace.coe_gramSchmidtBasis power) i

private theorem orthogonal_power_basis_orthogonal {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E) {i j : Fin q.natDegree} (hij : i ≠ j) :
    inner Real (orthogonalPowerBasis power i) (orthogonalPowerBasis power j) = 0 := by
  rw [orthogonal_power_basis_apply, orthogonal_power_basis_apply]
  exact InnerProductSpace.gramSchmidt_orthogonal Real power hij

private theorem orthogonal_power_basis_monic {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E) (i : Fin q.natDegree) :
    power.repr (orthogonalPowerBasis power i) i = 1 := by
  rw [orthogonal_power_basis_apply, InnerProductSpace.gramSchmidt_def]
  simp only [map_sub, map_sum, Finsupp.coe_sub, Pi.sub_apply, Basis.repr_self_apply, if_pos]
  have hprojection :
      (∑ j ∈ Finset.Iio i,
          power.repr ((Real ∙ InnerProductSpace.gramSchmidt Real power j).starProjection
            (power i))) i = 0 := by
    rw [Finset.sum_apply']
    apply Finset.sum_eq_zero
    intro j hj
    simp only [starProjection_singleton, map_smul, Finsupp.coe_smul, Pi.smul_apply]
    rw [InnerProductSpace.gramSchmidt_triangular (Finset.mem_Iio.mp hj) power]
    simp
  rw [hprojection, sub_zero]

private theorem orthogonal_power_basis_upper_zero {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E) {i j : Fin q.natDegree} (hij : i < j) :
    power.repr (orthogonalPowerBasis power i) j = 0 := by
  rw [orthogonal_power_basis_apply]
  exact InnerProductSpace.gramSchmidt_triangular hij power

private theorem squared_norm_pos {q : Real[X]}
    (power : Basis (Fin q.natDegree) Real E) (i : Fin q.natDegree) :
    0 < squaredNorm power i := by
  rw [squaredNorm, real_inner_self_pos]
  exact (orthogonalPowerBasis power).ne_zero i

private theorem multiplication_matrix_charpoly (q : Real[X]) (hq : q.Monic) :
    (coefficientMultiplicationMatrix q).charpoly = q := by
  let pb := AdjoinRoot.powerBasis hq.ne_zero
  have hminpolyGen : pb.minpolyGen = q := by
    rw [PowerBasis.minpolyGen_eq]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hq
  have hmatrix :
      coefficientMultiplicationMatrix q = Algebra.leftMulMatrix pb.basis pb.gen := by
    rw [pb.leftMulMatrix, hminpolyGen]
    rfl
  calc
    (coefficientMultiplicationMatrix q).charpoly =
        (Algebra.leftMulMatrix pb.basis pb.gen).charpoly :=
      congrArg Matrix.charpoly hmatrix
    _ = minpoly Real pb.gen := charpoly_leftMulMatrix pb
    _ = q := AdjoinRoot.minpoly_powerBasis_gen_of_monic hq

private theorem jacobi_entry_eq_inner_div (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E) (i j : Fin q.natDegree) :
    jacobiMatrix q power i j =
      inner Real (orthogonalPowerBasis power i)
          (coefficientMultiplication q power (orthogonalPowerBasis power j)) /
        squaredNorm power i := by
  rw [jacobiMatrix, LinearMap.toMatrix_apply]
  apply (eq_div_iff (ne_of_gt (squared_norm_pos power i))).2
  rw [mul_comm]
  conv_rhs =>
    rw [← (orthogonalPowerBasis power).sum_repr
      (coefficientMultiplication q power (orthogonalPowerBasis power j))]
  simp only [inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single i]
  · simp [squaredNorm, mul_comm]
  · intro k _ hki
    rw [orthogonal_power_basis_orthogonal power hki.symm, mul_zero]
  · simp

private theorem multiplication_power_coordinate_zero (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E) (j k : Fin q.natDegree)
    (hjk : j.1 + 1 < k.1) :
    power.repr
        (coefficientMultiplication q power (orthogonalPowerBasis power j)) k = 0 := by
  classical
  rw [coefficientMultiplication, Matrix.repr_toLin]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hlast : l.1 + 1 = q.natDegree
  · rw [coefficientMultiplicationMatrix, if_pos hlast]
    have hjl : j < l := Fin.mk_lt_mk.mpr (by omega)
    rw [orthogonal_power_basis_upper_zero power hjl]
    simp
  · by_cases hshift : k.1 = l.1 + 1
    · rw [coefficientMultiplicationMatrix, if_neg hlast, if_pos hshift]
      have hjl : j < l := Fin.mk_lt_mk.mpr (by omega)
      rw [orthogonal_power_basis_upper_zero power hjl]
      simp
    · rw [coefficientMultiplicationMatrix, if_neg hlast, if_neg hshift, zero_mul]

private theorem jacobi_lower_zero (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E) (j k : Fin q.natDegree)
    (hjk : j.1 + 1 < k.1) :
    jacobiMatrix q power k j = 0 := by
  rw [jacobiMatrix, LinearMap.toMatrix_apply]
  let next : Fin q.natDegree := ⟨j.1 + 1, lt_trans hjk k.isLt⟩
  have hdegreePower :
      coefficientMultiplication q power (orthogonalPowerBasis power j) ∈
        span Real (power '' Set.Iic next) := by
    rw [Basis.mem_span_image]
    intro l hl
    by_contra hnot
    have hnextl : next < l := lt_of_not_ge hnot
    have hjl : j.1 + 1 < l.1 := by
      change next.1 < l.1
      exact Fin.mk_lt_mk.mp hnextl
    exact (Finsupp.mem_support_iff.mp hl)
      (multiplication_power_coordinate_zero q power j l hjl)
  have hspan :
      span Real ((orthogonalPowerBasis power : Fin q.natDegree -> E) '' Set.Iic next) =
        span Real (power '' Set.Iic next) := by
    simpa only [orthogonalPowerBasis, InnerProductSpace.coe_gramSchmidtBasis] using
      (InnerProductSpace.span_gramSchmidt_Iic Real power next)
  have hdegreeOrthogonal :
      coefficientMultiplication q power (orthogonalPowerBasis power j) ∈
        span Real ((orthogonalPowerBasis power : Fin q.natDegree -> E) '' Set.Iic next) := by
    rw [hspan]
    exact hdegreePower
  have hsupport := (orthogonalPowerBasis power).repr_support_subset_of_mem_span
    (Set.Iic next) hdegreeOrthogonal
  by_contra hnonzero
  have hkSupport :
      k ∈ ((orthogonalPowerBasis power).repr
        (coefficientMultiplication q power (orthogonalPowerBasis power j))).support :=
    Finsupp.mem_support_iff.mpr hnonzero
  have hkLe := hsupport hkSupport
  simp only [Set.mem_Iic] at hkLe
  have hkLeVal : k.1 ≤ next.1 := Fin.mk_le_mk.mp hkLe
  change k.1 ≤ j.1 + 1 at hkLeVal
  exact (not_lt_of_ge hkLeVal) hjk

private theorem multiplication_previous_coordinate_one (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E)
    (j : Fin q.natDegree) (hj : 0 < j.1) :
    power.repr
        (coefficientMultiplication q power (orthogonalPowerBasis power (previousIndex j))) j =
      1 := by
  classical
  rw [coefficientMultiplication, Matrix.repr_toLin]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (previousIndex j)]
  · have hpreviousSucc : (previousIndex j).1 + 1 = j.1 := by
      simp [previousIndex, Nat.sub_add_cancel hj]
    have hnotLast : (previousIndex j).1 + 1 ≠ q.natDegree := by
      omega
    rw [coefficientMultiplicationMatrix, if_neg hnotLast,
      if_pos hpreviousSucc.symm, orthogonal_power_basis_monic]
    simp
  · intro l _ hl
    by_cases hlast : l.1 + 1 = q.natDegree
    · rw [coefficientMultiplicationMatrix, if_pos hlast]
      have hprevl : previousIndex j < l := by
        apply Fin.mk_lt_mk.mpr
        omega
      rw [orthogonal_power_basis_upper_zero power hprevl]
      simp
    · by_cases hshift : j.1 = l.1 + 1
      · exfalso
        apply hl
        apply Fin.ext
        simp only [previousIndex]
        omega
      · rw [coefficientMultiplicationMatrix, if_neg hlast, if_neg hshift, zero_mul]
  · simp

private theorem jacobi_subdiagonal_one (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E)
    (j : Fin q.natDegree) (hj : 0 < j.1) :
    jacobiMatrix q power j (previousIndex j) = 1 := by
  have hcoordinate :
      power.repr
          (coefficientMultiplication q power (orthogonalPowerBasis power (previousIndex j))) j =
        (orthogonalPowerBasis power).repr
          (coefficientMultiplication q power (orthogonalPowerBasis power (previousIndex j))) j := by
    conv_lhs =>
      rw [← (orthogonalPowerBasis power).sum_repr
        (coefficientMultiplication q power (orthogonalPowerBasis power (previousIndex j)))]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [orthogonal_power_basis_monic]
      simp
    · intro k _ hkj
      rcases hkj.lt_or_gt with hkj | hkj
      · rw [orthogonal_power_basis_upper_zero power hkj]
        simp
      · have hzero : jacobiMatrix q power k (previousIndex j) = 0 :=
          jacobi_lower_zero q power (previousIndex j) k (by simp [previousIndex]; omega)
        rw [jacobiMatrix, LinearMap.toMatrix_apply] at hzero
        rw [hzero]
        simp
    · simp
  rw [jacobiMatrix, LinearMap.toMatrix_apply, ← hcoordinate]
  exact multiplication_previous_coordinate_one q power j hj

private theorem jacobi_tridiagonal (q : Real[X])
    (power : Basis (Fin q.natDegree) Real E)
    (hSymmetric : forall x y,
      inner Real (coefficientMultiplication q power x) y =
        inner Real x (coefficientMultiplication q power y))
    (i j : Fin q.natDegree) (hfar : i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) :
    jacobiMatrix q power i j = 0 := by
  rcases hfar with hupper | hlower
  · have htranspose : jacobiMatrix q power j i = 0 :=
      jacobi_lower_zero q power i j hupper
    have hinnerZero :
        inner Real (orthogonalPowerBasis power j)
            (coefficientMultiplication q power (orthogonalPowerBasis power i)) = 0 := by
      have hentry := jacobi_entry_eq_inner_div q power j i
      rw [htranspose] at hentry
      rcases (div_eq_zero_iff.mp hentry.symm) with hzero | hnorm
      · exact hzero
      · exact False.elim ((ne_of_gt (squared_norm_pos power j)) hnorm)
    rw [jacobi_entry_eq_inner_div, ← hSymmetric, real_inner_comm, hinnerZero, zero_div]
  · exact jacobi_lower_zero q power j i hlower

/-- Under a strictly positive coefficient Hankel form, Gram--Schmidt applied to the power basis
constructs monic orthogonal polynomials. The coefficient-driven multiplication operator is
tridiagonal in that basis, its positive superdiagonal coefficient is the ratio of consecutive
squared norms, and its characteristic polynomial is the prescribed polynomial `q`. -/
theorem coefficient_driven_jacobi_characteristic_polynomial
    (q : Real[X]) (hq : q.Monic) (power : Basis (Fin q.natDegree) Real E)
    (moment : Nat -> Real)
    (hinner : forall x y, inner Real x y = coefficientHankelValue power moment x y)
    (hstrict : StrictPositiveHankel power moment)
    (hSymmetric : forall x y,
      inner Real (coefficientMultiplication q power x) y =
        inner Real x (coefficientMultiplication q power y)) :
    let p := orthogonalPowerBasis power
    let J := jacobiMatrix q power
    let h := squaredNorm power
    (forall i j, i ≠ j -> inner Real (p i) (p j) = 0) /\
      (forall i, power.repr (p i) i = 1) /\
      (forall i j, i.1 + 1 < j.1 ∨ j.1 + 1 < i.1 -> J i j = 0) /\
      (forall j (hj : 0 < j.1),
        let previous := previousIndex j
        J j previous = 1 /\
          J previous j = h j / h previous /\
          0 < J previous j) /\
      J.charpoly = q := by
  letI : Module.Finite Real E := Module.Finite.of_basis power
  letI : Module.Free Real E := Module.Free.of_basis power
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ hij => orthogonal_power_basis_orthogonal power hij
  · exact orthogonal_power_basis_monic power
  · exact jacobi_tridiagonal q power hSymmetric
  · intro j hj
    let previous := previousIndex j
    have hsub : jacobiMatrix q power j previous = 1 :=
      jacobi_subdiagonal_one q power j hj
    have hnormPrevious : 0 < squaredNorm power previous := by
      rw [squaredNorm, hinner]
      exact hstrict _ ((orthogonalPowerBasis power).ne_zero previous)
    have hnormJ : 0 < squaredNorm power j := by
      rw [squaredNorm, hinner]
      exact hstrict _ ((orthogonalPowerBasis power).ne_zero j)
    have hratio :
        jacobiMatrix q power previous j = squaredNorm power j / squaredNorm power previous := by
      have hinnerSub :
          inner Real (orthogonalPowerBasis power j)
              (coefficientMultiplication q power (orthogonalPowerBasis power previous)) =
            squaredNorm power j := by
        have hentry := jacobi_entry_eq_inner_div q power j previous
        rw [hsub] at hentry
        exact (div_eq_one_iff_eq (ne_of_gt hnormJ)).mp hentry.symm
      rw [jacobi_entry_eq_inner_div]
      rw [← hSymmetric]
      rw [real_inner_comm]
      rw [hinnerSub]
    exact ⟨hsub, hratio, hratio.symm ▸ div_pos hnormJ hnormPrevious⟩
  · rw [jacobiMatrix, LinearMap.charpoly_toMatrix, coefficientMultiplication,
      Matrix.charpoly_toLin]
    exact multiplication_matrix_charpoly q hq

#print axioms coefficient_driven_jacobi_characteristic_polynomial

end D5.S3.Constants.Moments.CoefficientDrivenJacobiCharacteristicPolynomial
