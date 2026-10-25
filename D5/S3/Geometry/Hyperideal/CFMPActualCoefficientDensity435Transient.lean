import D5.S3.Geometry.Hyperideal.CFMPCoefficientAreaDeterminant435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativeSurfaceJacobian435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPCoefficientAreaDeterminant435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativeSurfaceJacobian435Transient

namespace CFMPActualCoefficientDensity435Transient

def J : M4 := Matrix.diagonal ![(1:ℝ),1,1,-1]

theorem gram_matrix (S : M4) :
    (fun i j => lorentz (S i) (S j)) = S * J * S.transpose := by
  ext i j
  simp [Matrix.mul_apply,J,Matrix.diagonal_apply,Matrix.transpose_apply,
    lorentz,Fin.sum_univ_four]

theorem gram_det (S : M4) :
    Matrix.det (fun i j => lorentz (S i) (S j)) = -(S.det)^2 := by
  rw [gram_matrix,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hJ : J.det = -1 := by
    simp [J,Matrix.det_diagonal,Fin.prod_univ_four]
  rw [hJ]
  ring

theorem gram_det_with_normal (U P Q N : W)
    (hU : lorentz U N = 0) (hP : lorentz P N = 0)
    (hQ : lorentz Q N = 0) :
    (rows U P Q N).det^2 = -gram3 U P Q * lorentz N N := by
  have hNU : lorentz N U = 0 := (pairing_symm N U).trans hU
  have hNP : lorentz N P = 0 := (pairing_symm N P).trans hP
  have hNQ : lorentz N Q = 0 := (pairing_symm N Q).trans hQ
  have hPU := pairing_symm P U
  have hQU := pairing_symm Q U
  have hQP := pairing_symm Q P
  have hd : Matrix.det (fun i j => lorentz ((rows U P Q N) i) ((rows U P Q N) j)) =
      gram3 U P Q * lorentz N N := by
    calc
      _ = (Matrix.det !![lorentz U U,lorentz U P,lorentz U Q,0;
          lorentz U P,lorentz P P,lorentz P Q,0;
          lorentz U Q,lorentz P Q,lorentz Q Q,0;
          0,0,0,lorentz N N]) := by
        apply congrArg Matrix.det
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [rows,hU,hP,hQ,hNU,hNP,hNQ,hPU,hQU,hQP]
      _ = _ := by
        have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
        have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
        have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
        rw [Matrix.det_succ_row_zero (n := 3)]
        simp [Matrix.det_fin_three,Fin.sum_univ_four,Matrix.submatrix_apply,gram3,
          h12,h21,h22]
        <;> ring
  have hg := gram_det (rows U P Q N)
  rw [hd] at hg
  linarith

theorem actual_face_orthogonal (M : M4) (hM : M.det ≠ 0) (x v w : V) :
    let N := raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)
    lorentz ((lift x) ᵥ* M) N = 0 ∧
    lorentz ((tangent v) ᵥ* M) N = 0 ∧
    lorentz ((tangent w) ᵥ* M) N = 0 := by
  dsimp only
  rw [pair_raw M hM,pair_raw M hM,pair_raw M hM]
  constructor
  · simp [lift,covector,dotProduct,Fin.sum_univ_four,Fin.sum_univ_three]
    ring
  · constructor
    · have h := dot_self_cross v w
      simp only [dotProduct,Fin.sum_univ_three] at h
      simp [tangent,covector,dotProduct,Fin.sum_univ_four]
      nlinarith
    · have h := dot_cross_self v w
      simp only [dotProduct,Fin.sum_univ_three] at h
      simp [tangent,covector,dotProduct,Fin.sum_univ_four]
      nlinarith

theorem actual_face_gram (M : M4) (hM : M.det ≠ 0) (x v w : V)
    (hN : 0 < lorentz (raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x))
      (raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x))) :
    gram3 ((lift x) ᵥ* M) ((tangent v) ᵥ* M) ((tangent w) ᵥ* M) =
      -M.det^2 * lorentz (raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x))
        (raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)) := by
  let N := raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)
  obtain ⟨hU,hP,hQ⟩ := actual_face_orthogonal M hM x v w
  have hg := gram_det_with_normal ((lift x) ᵥ* M) ((tangent v) ᵥ* M)
    ((tangent w) ᵥ* M) N hU hP hQ
  have hd := actual_frame_normal_det M hM x v w
  change (rows ((lift x) ᵥ* M) ((tangent v) ᵥ* M)
    ((tangent w) ᵥ* M) N).det = -M.det * lorentz N N at hd
  rw [hd] at hg
  have he : lorentz N N *
      (gram3 ((lift x) ᵥ* M) ((tangent v) ᵥ* M) ((tangent w) ᵥ* M) +
        M.det^2 * lorentz N N) = 0 := by
    nlinarith [hg]
  have hz := (mul_eq_zero.mp he).resolve_left (ne_of_gt hN)
  change gram3 ((lift x) ᵥ* M) ((tangent v) ᵥ* M) ((tangent w) ᵥ* M) =
    -M.det^2 * lorentz N N
  linarith

theorem actual_face_density (M : M4) (hM : M.det ≠ 0) (x v w : V)
    (hN : 0 < lorentz (raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x))
      (raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)))
    (hr : 0 < radius ((lift x) ᵥ* M))
    (hd : delta ((lift x) ᵥ* M) ≠ 0)
    (R : W →ₗ[ℝ] W) (hR : ∀ u z, lorentz (R u) (R z) = lorentz u z)
    (hU : R ((lift x) ᵥ* M) 1 = 0)
    (hP : R ((tangent v) ᵥ* M) 1 = 0)
    (hQ : R ((tangent w) ᵥ* M) 1 = 0) :
    let U := (lift x) ᵥ* M
    let db := (nativeMatrix U).mulVec ((tangent v) ᵥ* M)
    let dc := (nativeMatrix U).mulVec ((tangent w) ᵥ* M)
    let N := raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)
    Real.sqrt (dotProduct (db ⨯₃ dc) (db ⨯₃ dc)) / (nativeMap U 2)^2 =
      |M.det| * Real.sqrt (lorentz N N) / (Real.sqrt (radius U))^3 := by
  have hj := native_surface_jacobian ((lift x) ᵥ* M) ((tangent v) ᵥ* M)
    ((tangent w) ᵥ* M) hr hd R hR hU hP hQ
  have hg := reflected_gram_det ((lift x) ᵥ* M) ((tangent v) ᵥ* M)
    ((tangent w) ᵥ* M) R hR hU hP hQ
  rw [actual_face_gram M hM x v w hN] at hg
  let C := (CFMPReflectedPlaneChart435Transient.augmented
    (planeColumns (R ((tangent v) ᵥ* M)) (R ((tangent w) ᵥ* M)))
    (dropPlane (R ((lift x) ᵥ* M)))).det
  let N := raw M (v ⨯₃ w) (dotProduct (v ⨯₃ w) x)
  have hs : |C|^2 = (|M.det| * Real.sqrt (lorentz N N))^2 := by
    rw [mul_pow,sq_abs,Real.sq_sqrt hN.le,sq_abs]
    change C^2 = M.det^2 * lorentz N N
    nlinarith [hg]
  have ha : |C| = |M.det| * Real.sqrt (lorentz N N) := by
    nlinarith [abs_nonneg C,mul_nonneg (abs_nonneg M.det) (Real.sqrt_nonneg (lorentz N N))]
  dsimp only at hj ⊢
  rw [show |(CFMPReflectedPlaneChart435Transient.augmented
    (planeColumns (R ((tangent v) ᵥ* M)) (R ((tangent w) ᵥ* M)))
    (dropPlane (R ((lift x) ᵥ* M)))).det| = |M.det| * Real.sqrt (lorentz N N) from ha] at hj
  exact hj

#print axioms actual_face_density
end CFMPActualCoefficientDensity435Transient
