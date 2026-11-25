/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Eval.Coeff, mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLinearEquiv]
   utility: none
   digest: Kernel certificates for the linear coefficient of a determinant pencil. -/

module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Exact first-order certificates for square minors of a matrix pencil. -/

set_option autoImplicit false
set_option linter.style.longLine false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor

open Polynomial
open scoped Matrix

variable {ι R K : Type*} [Fintype ι] [DecidableEq ι]

/-- A right kernel vector detects the linear coefficient of the determinant
by replacing a single column of the constant matrix. -/
theorem mul_coeff_one_det_pencil_eq_det_updateCol [CommRing R]
    (A E : Matrix ι ι R) (x : ι → R) (j : ι) (hx : A.mulVec x = 0) :
    x j * (A.map (C : R →+* R[X]) + (X : R[X]) • E.map (C : R →+* R[X])).det.coeff 1 =
      (A.updateCol j (E.mulVec x)).det := by
  let C₀ : R →+* R[X] := C
  let M : Matrix ι ι R[X] := A.map C₀ + (X : R[X]) • E.map C₀
  have hA : (A.map C₀).mulVec (C₀ ∘ x) = 0 := by
    funext i
    rw [← C₀.map_mulVec, hx]
    exact map_zero C₀
  have hE : (E.map C₀).mulVec (C₀ ∘ x) = C₀ ∘ E.mulVec x :=
    funext fun i => (C₀.map_mulVec E x i).symm
  have haction : M.mulVec (C₀ ∘ x) = (X : R[X]) • (C₀ ∘ E.mulVec x) := by
    simp only [M, Matrix.add_mulVec, Matrix.smul_mulVec, hA, hE, zero_add]
  have hdet : C (x j) * M.det = X * (M.updateCol j (C ∘ E.mulVec x)).det := by
    rw [← Matrix.det_updateCol_smul, ← haction]
    have hsum : M.mulVec (C₀ ∘ x) = fun k => ∑ i, (C₀ ∘ x) i • M k i := by
      funext k
      exact Finset.sum_congr rfl fun i _ => mul_comm (M k i) ((C₀ ∘ x) i)
    rw [hsum]
    exact (M.det_updateCol_sum j (C₀ ∘ x)).symm
  have hconstant : M.map (constantCoeff : R[X] →+* R) = A := by
    ext i k
    simp [M, C₀, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = (M.updateCol j (C ∘ E.mulVec x)).det.coeff 0 := by
      simpa only [coeff_C_mul, coeff_X_mul] using congrArg (fun p : R[X] => p.coeff (0 + 1)) hdet
    _ = _ := by
      change constantCoeff (M.updateCol j (C ∘ E.mulVec x)).det = _
      rw [RingHom.map_det]
      change ((M.updateCol j (C ∘ E.mulVec x)).map (constantCoeff : R[X] →+* R)).det = _
      rw [Matrix.map_updateCol, hconstant]
      simp [Function.comp_def]

/-- Independent retained columns and a nonzero left-right pairing certify a
nonzero linear coefficient of the full-order determinant. -/
theorem coeff_one_det_pencil_ne_zero_of_pairing [Field K]
    (A E : Matrix ι ι K) (x y : ι → K) (j : ι) (hx : A.mulVec x = 0)
    (hy : y ᵥ* A = 0) (hpair : y ⬝ᵥ E.mulVec x ≠ 0)
    (hcols : LinearIndependent K (fun i : {i : ι // i ≠ j} => A.col i.1)) :
    (A.map (C : K →+* K[X]) + (X : K[X]) • E.map (C : K →+* K[X])).det.coeff 1 ≠ 0 := by
  let B := A.updateCol j (E.mulVec x)
  have hdet : B.det ≠ 0 := by
    intro hzero
    obtain ⟨z, hz, hBz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    have hzj : z j = 0 := by
      have heq : y ⬝ᵥ (B.mulVec z) = (y ⬝ᵥ E.mulVec x) * z j := by
        change y ⬝ᵥ ((A.updateCol j (E.mulVec x)).mulVec z) = _
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_updateCol, hy]
        simp [dotProduct, Function.update_apply, ite_mul]
      rw [hBz, dotProduct_zero] at heq
      exact (mul_eq_zero.mp heq.symm).resolve_left hpair
    have hsum : ∑ i : {i : ι // i ≠ j}, z i.1 • A.col i.1 = 0 := by
      funext r
      have hr := congrFun hBz r
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hr
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j, hzj, mul_zero, zero_add] at hr
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, Pi.zero_apply]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hr
      change z i.1 * A r i.1 = A.updateCol j (E.mulVec x) r i.1 * z i.1
      rw [Matrix.updateCol_ne i.2, mul_comm]
    have hretained := Fintype.linearIndependent_iff.mp hcols (fun i => z i.1) hsum
    apply hz
    funext i
    by_cases hij : i = j
    · simpa only [hij, Pi.zero_apply] using hzj
    · exact hretained ⟨i, hij⟩
  intro hcoeff
  apply hdet
  simpa only [hcoeff, mul_zero] using
    (mul_coeff_one_det_pencil_eq_det_updateCol A E x j hx).symm

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor
