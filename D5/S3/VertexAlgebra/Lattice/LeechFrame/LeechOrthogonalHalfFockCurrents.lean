/- GID: D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechFrame/LeechOrthogonalHalfFockCurrents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized frame currents on the actual half-Fock space. -/

import D5.S3.VertexAlgebra.Lattice.LeechFrame.ActualLeechNormFourFrame
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormal

/-! Native half-Fock oscillator modes in orthonormal coordinates. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeHalfFock

open LatticeGeneratingFieldLocality LatticeLightConeCoordinates MvPolynomial
open LatticeActualAnnihilation (annihilationDerivation annihilation_apply)
open scoped BigOperators

variable {D : LatticeData}

/-- Complex-linear extension of the native modes in their polarization vector. -/
def polarizedCurrent (m : ℤ) : E D →ₗ[ℂ] Module.End ℂ (Oscillator D) where
  toFun u := ∑ i, u i • current D i m
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a u := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem polarizedCurrent_standardBasis (i : Fin D.rank) (m : ℤ) :
    polarizedCurrent m (standardBasis D i) = current D i m := by
  change (∑ j, standardBasis D i j • current D j m) = _
  simp [standardBasis, Pi.single_apply]

private theorem polarizedCurrent_negative_apply (u : E D) (k : ℕ) (P : Oscillator D) :
    polarizedCurrent (-(k : ℤ) - 1) u P = lin k u * P := by
  change (∑ i, u i • current D i (-(k : ℤ) - 1)) P = (∑ i, u i • X (i, k)) * P
  simp only [current_negative, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply, Finset.sum_mul, smul_mul_assoc]

private theorem polarizedCurrent_nonnegative_apply (u : E D) (k : ℕ) (P : Oscillator D) :
    polarizedCurrent (k : ℤ) u P = frequency (k : ℤ) • oldDerivative u k P := by
  change (∑ i, u i • current D i (k : ℤ)) P =
    frequency (k : ℤ) • (Derivation.coeFnAddMonoidHom
      (∑ i, u i • annihilationDerivation D i k)) P
  simp only [current, ite_eq_right (show ¬ (k : ℤ) < 0 by omega), Int.toNat_natCast,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, Finset.sum_apply,
    Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, annihilation_apply,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (u i) (frequency (k : ℤ)) _

section Coordinates

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E D))

private theorem inverse_X (c : ι) (k : ℕ) :
    (polynomialEquiv b).symm (X (c, k)) = lin k (b c) := by
  change aeval (fun x : ι × ℕ => lin x.2 (b x.1)) (X (c, k)) = _
  exact aeval_X _ _

private theorem coordinateDerivative_X (u : E D) (k l : ℕ) (c : ι) :
    coordinateDerivative b u k (X (c, l)) =
      if k = l then g D u (b c) • (1 : PolynomialCoordinates ι) else 0 := by
  classical
  by_cases h : k = l
  · subst l
    simp [coordinateDerivative, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  · simp [coordinateDerivative, pderiv_X, Prod.mk.injEq, h]

private theorem derivative_inverse (u : E D) (k : ℕ) (Q : PolynomialCoordinates ι) :
    oldDerivative u k ((polynomialEquiv b).symm Q) =
      (polynomialEquiv b).symm (coordinateDerivative b u k Q) := by
  induction Q using MvPolynomial.induction_on with
  | C z =>
    simp only [← algebraMap_eq, AlgEquiv.commutes, Derivation.map_algebraMap, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X Q x ih =>
    obtain ⟨c, l⟩ := x
    have hx : oldDerivative u k ((polynomialEquiv b).symm (X (c, l))) =
        (polynomialEquiv b).symm (coordinateDerivative b u k (X (c, l))) := by
      rw [inverse_X, oldDerivative_lin, coordinateDerivative_X]
      split_ifs <;> simp
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, ih, hx]

/-- The native mode polarized by the actual vector `b c`, conjugated by the
frequencywise polynomial change of coordinates. -/
def coordinateCurrent (c : ι) (m : ℤ) : Module.End ℂ (PolynomialCoordinates ι) :=
  (polynomialEquiv b).toLinearEquiv.conj (polarizedCurrent m (b c))

theorem coordinateCurrent_apply (c : ι) (m : ℤ) (Q : PolynomialCoordinates ι) :
    coordinateCurrent b c m Q =
      polynomialEquiv b (polarizedCurrent m (b c) ((polynomialEquiv b).symm Q)) := rfl

/-- Creation is multiplication by the corresponding basis variable. -/
theorem coordinateCurrent_negative (c : ι) (k : ℕ) :
    coordinateCurrent b c (-(k : ℤ) - 1) = LinearMap.mulLeft ℂ (X (c, k)) := by
  apply LinearMap.ext
  intro Q
  have hx := congrArg (polynomialEquiv b) (inverse_X b c k)
  simp only [AlgEquiv.apply_symm_apply] at hx
  simp only [coordinateCurrent_apply, polarizedCurrent_negative_apply, map_mul, ← hx,
    AlgEquiv.apply_symm_apply, LinearMap.mulLeft_apply]

variable [DecidableEq ι]
variable (horth : ∀ c d : ι, g D (b c) (b d) = if d = c then 1 else 0)
include horth

/-- In a Gram-orthonormal basis, annihilation is the corresponding partial
derivative scaled by the native half-integral frequency. -/
theorem coordinateCurrent_nonnegative (c : ι) (k : ℕ) :
    coordinateCurrent b c (k : ℤ) =
      (k + 1 / 2 : ℂ) • (pderiv (c, k)).toLinearMap := by
  have hderiv : coordinateDerivative b (b c) k = pderiv (c, k) := by
    simp [coordinateDerivative, horth, ite_smul]
  apply LinearMap.ext
  intro Q
  rw [coordinateCurrent_apply, polarizedCurrent_nonnegative_apply, derivative_inverse,
    map_smul, AlgEquiv.apply_symm_apply, hderiv]
  simp [frequency]

/-- A factor independent of the polarization coordinate passes through every
mode unchanged, including the annihilation mode of frequency one half. -/
theorem coordinateCurrent_mul_of_notMem_vars (c : ι) (m : ℤ)
    (P R : PolynomialCoordinates ι) (hR : ∀ k : ℕ, (c, k) ∉ R.vars) :
    coordinateCurrent b c m (P * R) = coordinateCurrent b c m P * R := by
  cases m with
  | ofNat k =>
    change coordinateCurrent b c (k : ℤ) (P * R) = coordinateCurrent b c (k : ℤ) P * R
    simp only [coordinateCurrent_nonnegative b horth, LinearMap.smul_apply,
      Derivation.coeFn_coe, pderiv_mul, pderiv_eq_zero_of_notMem_vars (hR k),
      mul_zero, add_zero, smul_mul_assoc]
  | negSucc k =>
    rw [show Int.negSucc k = -(k : ℤ) - 1 by omega, coordinateCurrent_negative]
    simp [mul_assoc]

end Coordinates

end D5.S3.VertexAlgebra.LatticeHalfFock

namespace D5.S3.VertexAlgebra.ActualLeechHalfFockCurrents

open ActualLeechHyperbolic (leechData)
open ActualLeechNormFourFrame (Index complexBasis complexBasis_apply complexVector complex_pairing)
open LatticeLightConeCoordinates (E g PolynomialCoordinates)
open LatticeHalfFock
open MvPolynomial

/-- Normalize the actual norm-four Leech frame by scaling its complex basis. -/
def orthonormalBasis : Module.Basis Index ℂ (E leechData) :=
  complexBasis.map (LinearEquiv.smulOfUnit (Units.mk0 (1 / 2 : ℂ) (by norm_num)))

@[simp] theorem orthonormalBasis_apply (c : Index) :
    orthonormalBasis c = (1 / 2 : ℂ) • complexVector c := by
  rw [orthonormalBasis, Module.Basis.map_apply, complexBasis_apply]
  rfl

theorem orthonormalBasis_pairing (c d : Index) :
    g leechData (orthonormalBasis c) (orthonormalBasis d) = if d = c then 1 else 0 := by
  rw [orthonormalBasis_apply, orthonormalBasis_apply, LatticeLightConeCoordinates.g_smul_left,
    LatticeLightConeCoordinates.g_smul_right, complex_pairing]
  by_cases h : d = c
  · subst d
    norm_num
  · simp [h, Ne.symm h]

theorem current_negative (c : Index) (k : ℕ) :
    coordinateCurrent orthonormalBasis c (-(k : ℤ) - 1) =
      LinearMap.mulLeft ℂ (X (c, k)) :=
  coordinateCurrent_negative orthonormalBasis c k

theorem current_nonnegative (c : Index) (k : ℕ) :
    coordinateCurrent orthonormalBasis c (k : ℤ) =
      (k + 1 / 2 : ℂ) • (pderiv (c, k)).toLinearMap :=
  coordinateCurrent_nonnegative orthonormalBasis orthonormalBasis_pairing c k

theorem current_mul_of_notMem_vars (c : Index) (m : ℤ) (P R : PolynomialCoordinates Index)
    (hR : ∀ k : ℕ, (c, k) ∉ R.vars) :
    coordinateCurrent orthonormalBasis c m (P * R) =
      coordinateCurrent orthonormalBasis c m P * R :=
  coordinateCurrent_mul_of_notMem_vars orthonormalBasis orthonormalBasis_pairing c m P R hR

end D5.S3.VertexAlgebra.ActualLeechHalfFockCurrents
