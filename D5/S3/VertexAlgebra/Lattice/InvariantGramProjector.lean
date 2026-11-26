import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Complex.Module

/-! Source draft for the invariant weight-two obstruction. -/

set_option autoImplicit false

namespace InvariantGramProjectorDraft

open LinearMap (BilinForm)
open scoped Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem nondegenerate_of_pos (B : BilinForm ℝ V)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) : B.Nondegenerate := by
  classical
  constructor <;> intro x hx <;> by_contra hne <;>
    exact (ne_of_gt (hpos x hne)) (hx x)

variable [FiniteDimensional ℝ V] {ι : Type*}

/-- An invariant subspace of a positive definite symmetric real form admits
an equivariant orthogonal projector. The membership equivalence expresses
invariance under the action and its inverse. -/
theorem exists_invariant_projector
    (B : BilinForm ℝ V) (hs : B.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (W : Submodule ℝ V) (hW₀ : W ≠ ⊥) (hW₁ : W ≠ ⊤)
    (g : ι → V ≃ₗ[ℝ] V)
    (hg : ∀ t x y, B (g t x) (g t y) = B x y)
    (hW : ∀ t x, g t x ∈ W ↔ x ∈ W) :
    ∃ P : Module.End ℝ V, LinearMap.range P = W ∧
      P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧
      (∀ x y, B (P x) y = B x (P y)) ∧
      (∀ t, Commute (g t).toLinearMap P) := by
  classical
  have hnd : (B.restrict W).Nondegenerate := by
    apply nondegenerate_of_pos
    intro x hx
    exact hpos (x : V) (fun h => hx (Subtype.ext h))
  have hc : IsCompl W (B.orthogonal W) :=
    BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hnd
  let P : Module.End ℝ V := W.projection (B.orthogonal W) hc
  have hmem (x : V) : P x ∈ W := Submodule.projection_apply_mem hc x
  have hsub (x : V) : x - P x ∈ B.orthogonal W :=
    Submodule.sub_projection_mem hc x
  have hRange : LinearMap.range P = W := Submodule.range_projection hc
  have hP₀ : P ≠ 0 := by
    intro hz
    apply hW₀
    simpa only [hz, LinearMap.range_zero] using hRange.symm
  have hP₁ : P ≠ 1 := by
    intro hone
    have hr := hRange
    rw [hone] at hr
    change LinearMap.range (LinearMap.id : V →ₗ[ℝ] V) = W at hr
    exact hW₁ (hr.symm.trans LinearMap.range_id)
  have horth (t : ι) {x : V} (hx : x ∈ B.orthogonal W) :
      g t x ∈ B.orthogonal W := by
    rw [BilinForm.mem_orthogonal_iff] at hx ⊢
    intro w hw
    have hw' : (g t).symm w ∈ W := (hW t ((g t).symm w)).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using hw)
    calc
      B w (g t x) = B (g t ((g t).symm w)) (g t x) := by
        rw [LinearEquiv.apply_symm_apply]
      _ = B ((g t).symm w) x := hg t _ _
      _ = 0 := hx _ hw'
  refine ⟨P, hRange, Submodule.isIdempotentElem_projection hc, hP₀, hP₁, ?_, ?_⟩
  · intro x y
    have hy : B (P x) (y - P y) = 0 :=
      BilinForm.mem_orthogonal_iff.mp (hsub y) (P x) (hmem x)
    have hx : B (x - P x) (P y) = 0 := by
      rw [hs.eq (x - P x) (P y)]
      exact BilinForm.mem_orthogonal_iff.mp (hsub x) (P y) (hmem y)
    rw [BilinForm.sub_right, sub_eq_zero] at hy
    rw [BilinForm.sub_left, sub_eq_zero] at hx
    exact hy.trans hx.symm
  · intro t
    change (g t).toLinearMap * P = P * (g t).toLinearMap
    ext x
    change g t (P x) = P (g t x)
    have hzero : P (g t (x - P x)) = 0 :=
      Submodule.projection_apply_of_mem_right hc (horth t (hsub x))
    simp only [map_sub, sub_eq_zero] at hzero
    have hfixed : P (g t (P x)) = g t (P x) :=
      Submodule.projection_apply_of_mem_left hc ((hW t (P x)).mpr (hmem x))
    exact (hzero.trans hfixed).symm

/-- In any real basis, the projector satisfies the real matrix hypotheses of
`projector_fixed_weight_two`. The Gram matrix is the matrix of the form. -/
theorem exists_invariant_projector_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ V)
    (B : BilinForm ℝ V) (hs : B.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (W : Submodule ℝ V) (hW₀ : W ≠ ⊥) (hW₁ : W ≠ ⊤)
    (g : ι → V ≃ₗ[ℝ] V)
    (hg : ∀ t x y, B (g t x) (g t y) = B x y)
    (hW : ∀ t x, g t x ∈ W ↔ x ∈ W) :
    ∃ P : Matrix n n ℝ, P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧
      Pᵀ * B.toMatrix b = B.toMatrix b * P ∧
      (∀ t, Commute (LinearMap.toMatrix b b (g t).toLinearMap) P) := by
  obtain ⟨p, _, hp, hp₀, hp₁, hself, hcomm⟩ :=
    exists_invariant_projector B hs hpos W hW₀ hW₁ g hg hW
  let T := LinearMap.toMatrixAlgEquiv b
  have hleft : B.compLeft p = B.compRight p := by
    apply BilinForm.ext
    exact hself
  refine ⟨T p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hp]
  · intro hz
    exact hp₀ (T.injective (hz.trans (map_zero T).symm))
  · intro hone
    exact hp₁ (T.injective (hone.trans (map_one T).symm))
  · change (LinearMap.toMatrix b b p)ᵀ * B.toMatrix b =
      B.toMatrix b * LinearMap.toMatrix b b p
    rw [← BilinForm.toMatrix_compLeft b B p,
      ← BilinForm.toMatrix_compRight b B p, hleft]
  · intro t
    change Commute (T (g t).toLinearMap) (T p)
    change T (g t).toLinearMap * T p = T p * T (g t).toLinearMap
    rw [← map_mul, ← map_mul, (hcomm t).eq]

/-- Entrywise extension to complex coefficients gives the same projector
equations for the complexified Gram and action matrices. -/
theorem exists_invariant_projector_complex_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ V)
    (B : BilinForm ℝ V) (hs : B.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (W : Submodule ℝ V) (hW₀ : W ≠ ⊥) (hW₁ : W ≠ ⊤)
    (g : ι → V ≃ₗ[ℝ] V)
    (hg : ∀ t x y, B (g t x) (g t y) = B x y)
    (hW : ∀ t x, g t x ∈ W ↔ x ∈ W) :
    ∃ P : Matrix n n ℂ, P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧
      Pᵀ * (B.toMatrix b).map Complex.ofRealHom =
        (B.toMatrix b).map Complex.ofRealHom * P ∧
      (∀ t, Commute ((LinearMap.toMatrix b b (g t).toLinearMap).map Complex.ofRealHom) P) := by
  obtain ⟨p, hp, hp₀, hp₁, hself, hcomm⟩ :=
    exists_invariant_projector_matrix b B hs hpos W hW₀ hW₁ g hg hW
  let F : Matrix n n ℝ →+* Matrix n n ℂ := Complex.ofRealHom.mapMatrix
  have hF : Function.Injective F := Matrix.map_injective Complex.ofReal_injective
  refine ⟨F p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hp]
  · intro hz
    exact hp₀ (hF (hz.trans (map_zero F).symm))
  · intro hone
    exact hp₁ (hF (hone.trans (map_one F).symm))
  · change (p.map Complex.ofRealHom)ᵀ * (B.toMatrix b).map Complex.ofRealHom =
      (B.toMatrix b).map Complex.ofRealHom * p.map Complex.ofRealHom
    simpa only [Matrix.map_mul, Matrix.transpose_map] using
      congrArg (fun A : Matrix n n ℝ => A.map Complex.ofRealHom) hself
  · intro t
    change F (LinearMap.toMatrix b b (g t).toLinearMap) * F p =
      F p * F (LinearMap.toMatrix b b (g t).toLinearMap)
    rw [← map_mul, ← map_mul, (hcomm t).eq]

/- To apply the last theorem to the lattice, choose its real charge basis and
real Gram form; identify their complex matrices with `gramComplex D` and
`mixingMatrix D (g t)`. An inverse symmetric Gram matrix H then supplies
`hH` and `hHG` in `projector_fixed_weight_two`, giving the states
`omega D H` and `omega D (P * H)`. -/

end InvariantGramProjectorDraft

#print axioms InvariantGramProjectorDraft.nondegenerate_of_pos
#print axioms InvariantGramProjectorDraft.exists_invariant_projector
#print axioms InvariantGramProjectorDraft.exists_invariant_projector_matrix
#print axioms InvariantGramProjectorDraft.exists_invariant_projector_complex_matrix
