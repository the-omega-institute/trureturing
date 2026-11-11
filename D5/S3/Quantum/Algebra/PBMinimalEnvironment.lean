/- GID: D5/S3/Quantum/Algebra/PBMinimalEnvironment
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBMinimalEnvironment
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: The three actor moments characterize and determine the dimension of a minimal environment. -/

import D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance
import Mathlib.Analysis.Matrix.Order
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Algebra.Polynomial.Roots

/-! The zero kernel-coupling branch of the finite three-moment realization problem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace Matrix ComplexOrder Polynomial
open Module (finrank)

namespace D5.S3.Quantum.Algebra.PBMinimalEnvironment

private theorem exists_real_det_ne_zero_of_complex {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (H Q : E →ₗ[ℂ] E) (h : LinearMap.det (H + Complex.I • Q) ≠ 0) :
    ∃ t : ℝ, LinearMap.det (H + (t : ℂ) • Q) ≠ 0 := by
  classical
  let b := Module.finBasis ℂ E
  let hM := LinearMap.toMatrix b b H
  let qM := LinearMap.toMatrix b b Q
  let p := (hM.map (Polynomial.C : ℂ →+* ℂ[X]) +
    (Polynomial.X : ℂ[X]) • qM.map (Polynomial.C : ℂ →+* ℂ[X])).det
  have hp (z : ℂ) : p.eval z = LinearMap.det (H + z • Q) := by
    rw [← LinearMap.det_toMatrix b]
    rw [show p.eval z = Polynomial.evalRingHom z p by rfl, p, RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, hM, qM]
  have hn : p ≠ 0 := by
    intro he
    exact h (by simpa [he] using (hp Complex.I).symm)
  by_contra! ht
  have hInf : Set.Infinite ((fun x : ℝ => (x : ℂ)) '' Set.univ) :=
    Set.infinite_univ.image (Complex.ofReal_injective.injOn)
  exact hn (Polynomial.eq_zero_of_infinite_isRoot p (hInf.mono (by
    rintro _ ⟨t, -, rfl⟩
    exact (hp _).trans (ht t))))

/-- An injective symmetric map on a subspace extends to an invertible symmetric
operator on the same finite space. Its image need not lie in the subspace. -/
private theorem exists_symmetric_bijective_extension {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (M : Submodule ℂ E) (A : M →ₗ[ℂ] E) (hi : Function.Injective A)
    (hs : ∀ x y : M, ⟪A x, (y : E)⟫_ℂ = ⟪(x : E), A y⟫_ℂ) :
    ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧ Function.Bijective T ∧
      ∀ x : M, T x = A x := by
  let P : E →ₗ[ℂ] E := M.starProjection.toLinearMap
  let Q : E →ₗ[ℂ] E := Mᗮ.starProjection.toLinearMap
  let L : E →ₗ[ℂ] E := A.comp M.orthogonalProjectionOnto.toLinearMap
  have hP : P.IsSymmetric := M.starProjection_isSymmetric
  have hQ : Q.IsSymmetric := Mᗮ.starProjection_isSymmetric
  have hPL : (P.comp L).IsSymmetric := by
    intro x y
    change ⟪P (L x), y⟫_ℂ = ⟪x, P (L y)⟫_ℂ
    rw [hP, ← hP x (L y)]
    exact hs (M.orthogonalProjectionOnto x) (M.orthogonalProjectionOnto y)
  let H : E →ₗ[ℂ] E := L + L.adjoint - P.comp L
  have hH : H.IsSymmetric := by
    have hsum : (L + L.adjoint).IsSymmetric := by
      intro x y
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
      exact add_comm _ _
    exact hsum.sub hPL
  have hExt (x : M) : H x = A x := by
    have hL : L x = A x := by
      simp [L, M.orthogonalProjectionOnto_mem_subspace_eq_self x]
    have he : L.adjoint x = P (L x) := by
      apply ext_inner_left ℂ
      intro y
      rw [LinearMap.adjoint_inner_right, ← hP y (L x), hL]
      exact hs (M.orthogonalProjectionOnto y) x
    simp [H, he, hL]
  have hImag : Function.Injective (H + Complex.I • Q : E →ₗ[ℂ] E) := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply] at hx
    have hQQ : Q (Q x) = Q x :=
      Submodule.starProjection_eq_self_iff.mpr (Mᗮ.starProjection_apply_mem x)
    have hInner : ⟪x, Q x⟫_ℂ = ⟪Q x, Q x⟫_ℂ := by rw [hQ x (Q x), hQQ]
    have hx' : (⟪x, H x⟫_ℂ + Complex.I * ⟪Q x, Q x⟫_ℂ).im = 0 := by
      simpa [inner_add_right, inner_smul_right, hInner] using
        congrArg (fun y : E => (⟪x, y⟫_ℂ).im) hx
    have hnorm : ‖Q x‖ ^ 2 = 0 := by
      have hh : (⟪x, H x⟫_ℂ).im = 0 := hH.im_inner_self_apply x
      have hsq : ⟪Q x, Q x⟫_ℂ = ((‖Q x‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
      rw [hsq, Complex.add_im, hh, Complex.I_mul_im, Complex.ofReal_re, zero_add] at hx'
      exact hx' 
    have hqx : Q x = 0 := norm_eq_zero.mp (by nlinarith)
    have hxm : x ∈ M := by
      have hz : Mᗮ.starProjection x = 0 := hqx
      rw [Submodule.starProjection_orthogonal_val, sub_eq_zero] at hz
      exact Submodule.starProjection_eq_self_iff.mp hz.symm
    have hz : A ⟨x, hxm⟩ = 0 := by simpa [hqx, hExt ⟨x, hxm⟩] using hx
    change x = 0
    exact congrArg Subtype.val (hi (hz.trans A.map_zero.symm))
  have hdet : LinearMap.det (H + Complex.I • Q) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff]
    exact LinearMap.ker_eq_bot.mpr hImag
  obtain ⟨t, ht⟩ := exists_real_det_ne_zero_of_complex H Q hdet
  have hti : Function.Injective (H + (t : ℂ) • Q : E →ₗ[ℂ] E) := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff] at ht
    exact LinearMap.ker_eq_bot.mp ht
  refine ⟨H + (t : ℂ) • Q, hH.add (hQ.smul (by simp)),
    ⟨hti, LinearMap.injective_iff_surjective.mp hti⟩, ?_⟩
  intro x
  have hqx : Q x = 0 := by
    change Mᗮ.starProjection (x : E) = 0
    rw [Submodule.starProjection_orthogonal_val, M.starProjection_mem_subspace_eq_self x, sub_self]
  simp [hqx, hExt]

end D5.S3.Quantum.Algebra.PBMinimalEnvironment
