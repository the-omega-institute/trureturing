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
open scoped BigOperators Pointwise
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

private lemma sos4_zero (ι : Type*) : (0 : MvPolynomial ι ℝ) ∈ sos4 ι := by
  apply subset_convexHull ℝ _
  exact ⟨0, isHomogeneous_zero ι ℝ 2, by simp⟩

private lemma sos4_smul {ι : Type*} {f : MvPolynomial ι ℝ}
    (hf : f ∈ sos4 ι) (a : ℝ) (ha : 0 ≤ a) : a • f ∈ sos4 ι := by
  let S : Set (MvPolynomial ι ℝ) := {g | ∃ θ, θ.IsHomogeneous 2 ∧ g = θ ^ 2}
  have hS : a • S ⊆ S := by
    rintro g ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨C (Real.sqrt a) * θ, hθ.C_mul _, ?_⟩
    change a • θ ^ 2 = _
    rw [smul_eq_C_mul, mul_pow, ← map_pow, Real.sq_sqrt ha]
  have h := convexHull_mono (𝕜 := ℝ) hS
  rw [convexHull_smul] at h
  exact h ⟨f, hf, rfl⟩

private lemma sos4_add {ι : Type*} {f g : MvPolynomial ι ℝ}
    (hf : f ∈ sos4 ι) (hg : g ∈ sos4 ι) : f + g ∈ sos4 ι := by
  have h := (convex_convexHull ℝ _ ) hf hg
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have h2 := sos4_smul h 2 (by norm_num)
  convert h2 using 1
  module

private lemma linear_mul_sos {ι : Type*} (l : MvPolynomial ι ℝ)
    (hl : l.IsHomogeneous 1) (M : List (MvPolynomial ι ℝ))
    (hM : ∀ m ∈ M, m.IsHomogeneous 1) :
    l ^ 2 * (M.map (· ^ 2)).sum ∈ sos4 ι := by
  induction M with
  | nil => simpa using sos4_zero ι
  | cons m M ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    apply sos4_add
    · apply subset_convexHull ℝ _
      refine ⟨l * m, hl.mul (hM m (by simp)), ?_⟩
      exact (mul_pow l m 2).symm
    · exact ih (fun m hm => hM m (by simp [hm]))

private lemma sos_product {ι : Type*} (L M : List (MvPolynomial ι ℝ))
    (hL : ∀ l ∈ L, l.IsHomogeneous 1) (hM : ∀ m ∈ M, m.IsHomogeneous 1) :
    (L.map (· ^ 2)).sum * (M.map (· ^ 2)).sum ∈ sos4 ι := by
  induction L with
  | nil => simpa using sos4_zero ι
  | cons l L ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact sos4_add (linear_mul_sos l (hL l (by simp)) M hM)
      (ih (fun l hl => hL l (by simp [hl])))

end D5.S3.QuadraticForms.ConicGDNN.Duality
