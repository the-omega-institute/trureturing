/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary bilinear transpose for the literal infinite Gaussian and its inverse. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDifferentiation

/-! Kernel symmetry passes through a norm-summable rank-one series and the genuine inverse law. -/

noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDifferentiation
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

private lemma matrixEntry_comm (z : ℂ) (s t : ℕ) :
    matrixEntry z s t = matrixEntry z t s := by
  simp only [matrixEntry]
  rw [pairScalar_comm s t, Nat.add_comm s t,
    mul_comm (Real.sqrt (s : ℝ) : ℂ) (Real.sqrt (t : ℝ) : ℂ)]

lemma sourceBilinearFunctional_comm (x y : H) :
    sourceBilinearFunctional x y = sourceBilinearFunctional y x := by
  rw [sourceBilinearFunctional_apply, sourceBilinearFunctional_apply]
  exact tsum_congr (fun n => mul_comm (x n) (y n))

private lemma sourceBilinearFunctional_sub_left (u v x : H) :
    sourceBilinearFunctional (u - v) x =
      sourceBilinearFunctional u x - sourceBilinearFunctional v x := by
  rw [sourceBilinearFunctional_comm (u - v) x, map_sub,
    sourceBilinearFunctional_comm x u, sourceBilinearFunctional_comm x v]

private lemma sourceBilinearFunctional_term
    (z : ℂ) (i j : ℕ) (x y : H) :
    sourceBilinearFunctional x (term z (i, j) y) =
      matrixEntry z (i + 1) (j + 1) * x i * y j := by
  rw [sourceBilinearFunctional_apply, tsum_eq_single i]
  · rw [term_apply, ite_eq_left rfl]
    ring
  · intro n hni
    rw [term_apply, ite_eq_right (Ne.symm hni), mul_zero]

theorem operator_bilinear_transpose {z : ℂ} (hz : ‖z‖ < 1)
    (x y : H) :
    sourceBilinearFunctional x (operator z y) =
      sourceBilinearFunctional (operator z x) y := by
  let L : (H →L[ℂ] H) →L[ℂ] ℂ :=
    (sourceBilinearFunctional x).comp (ContinuousLinearMap.apply ℂ H y)
  let M : (H →L[ℂ] H) →L[ℂ] ℂ :=
    (sourceBilinearFunctional y).comp (ContinuousLinearMap.apply ℂ H x)
  have hs : Summable (fun p : ℕ × ℕ => term z p) :=
    (term_summable hz).of_norm
  have he (p : ℕ × ℕ) :
      L (term z p) = M (term z (p.2, p.1)) := by
    rcases p with ⟨i, j⟩
    change sourceBilinearFunctional x (term z (i, j) y) =
      sourceBilinearFunctional y (term z (j, i) x)
    rw [sourceBilinearFunctional_term, sourceBilinearFunctional_term,
      matrixEntry_comm z (i + 1) (j + 1)]
    ring
  calc
    _ = L (∑' p : ℕ × ℕ, term z p) := rfl
    _ = ∑' p : ℕ × ℕ, L (term z p) := L.map_tsum hs
    _ = ∑' p : ℕ × ℕ, M (term z (p.2, p.1)) := tsum_congr he
    _ = ∑' p : ℕ × ℕ, M (term z p) :=
      (Equiv.prodComm ℕ ℕ).tsum_eq (fun p => M (term z p))
    _ = M (∑' p : ℕ × ℕ, term z p) := (M.map_tsum hs).symm
    _ = sourceBilinearFunctional (operator z x) y :=
      sourceBilinearFunctional_comm y (operator z x)

theorem resolvent_bilinear_transpose {z : ℂ} (hz : ‖z‖ < 1)
    (x y : H) :
    sourceBilinearFunctional x (resolvent z y) =
      sourceBilinearFunctional (resolvent z x) y := by
  have hR : (1 - operator z) * resolvent z = 1 := by
    simpa only [OriginalGaussianResolvent.resolvent] using
      (mul_neg_geom_series (operator z)
        (OriginalGaussianWeightedResolvent.operator_norm_lt_one hz))
  have hx : resolvent z x - operator z (resolvent z x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hR
    change resolvent z x - operator z (resolvent z x) = x at h
    exact h
  have hy : resolvent z y - operator z (resolvent z y) = y := by
    have h := congrArg (fun T : H →L[ℂ] H => T y) hR
    change resolvent z y - operator z (resolvent z y) = y at h
    exact h
  calc
    _ = sourceBilinearFunctional
        (resolvent z x - operator z (resolvent z x)) (resolvent z y) := by
      rw [hx]
    _ = sourceBilinearFunctional (resolvent z x) (resolvent z y) -
        sourceBilinearFunctional (operator z (resolvent z x)) (resolvent z y) :=
      sourceBilinearFunctional_sub_left _ _ _
    _ = sourceBilinearFunctional (resolvent z x) (resolvent z y) -
        sourceBilinearFunctional (resolvent z x) (operator z (resolvent z y)) := by
      rw [← operator_bilinear_transpose hz (resolvent z x) (resolvent z y)]
    _ = sourceBilinearFunctional (resolvent z x)
        (resolvent z y - operator z (resolvent z y)) := by
      rw [map_sub]
    _ = sourceBilinearFunctional (resolvent z x) y := by rw [hy]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
