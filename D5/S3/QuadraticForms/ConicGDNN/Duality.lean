/- GID: D5/S3/QuadraticForms/ConicGDNN/Duality
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ConicGDNN/Duality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Sum of squares products and cone preservation from dual trace positivity. -/

import D5.S3.QuadraticForms.ConicGDNN.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
open D5.S3.QuadraticForms.ConicGDNN.Defs
namespace D5.S3.QuadraticForms.ConicGDNN.Duality

private lemma jsq_homogeneous {p r : ℕ} {k : Fin r → ℕ} (a : Idx p r k) :
    (jsq a).IsHomogeneous 2 := by
  rcases a with i | ⟨j, _ | i⟩
  · exact isHomogeneous_X_pow _ 2
  · exact IsHomogeneous.sum _ _ _ (fun o _ => isHomogeneous_X_pow _ 2)
  · change (C 2 * (X (Sum.inr ⟨j, none⟩) : MvPolynomial (Idx p r k) ℝ) * (X (Sum.inr ⟨j, some i⟩) : MvPolynomial (Idx p r k) ℝ)).IsHomogeneous 2
    exact ((isHomogeneous_X ℝ _).C_mul 2).mul (isHomogeneous_X ℝ _)

private lemma pullback_homogeneous {p r : ℕ} {k : Fin r → ℕ} (w : Idx p r k → ℝ) :
    (∑ a, C (w a) * jsq a).IsHomogeneous 2 := by
  exact IsHomogeneous.sum _ _ _ (fun a _ => (jsq_homogeneous a).C_mul (w a))

private lemma quartic_vecMulVec {p r : ℕ} {k : Fin r → ℕ}
    (u v : Idx p r k → ℝ) :
    quartic (vecMulVec u v) = (∑ a, C (u a) * jsq a) * (∑ b, C (v b) * jsq b) := by
  classical
  simp only [quartic, vecMulVec_apply, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Every rank-one symmetric matrix belongs to the zeroth approximation. -/
theorem quartic_rankOne {p r : ℕ} {k : Fin r → ℕ} (w : Idx p r k → ℝ) :
    vecMulVec w w ∈ knn0 p r k := by
  classical
  constructor
  · exact transpose_vecMulVec w w
  · apply subset_convexHull ℝ _
    refine ⟨∑ a, C (w a) * jsq a, pullback_homogeneous w, ?_⟩
    rw [quartic_vecMulVec, pow_two]

/-- Dual positivity on rank-one tests implies positive semidefiniteness. -/
theorem posSemidef_of_mem_dnnNN {p r : ℕ} {k : Fin r → ℕ}
    {Xm : Matrix (Idx p r k) (Idx p r k) ℝ} (hXm : Xm ∈ dnnNN p r k) :
    Xm.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.mpr hXm.1)
  intro w
  have h := hXm.2 _ (quartic_rankOne w)
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm] at h
  simpa only [star_trivial] using h

end D5.S3.QuadraticForms.ConicGDNN.Duality
