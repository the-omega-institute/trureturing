/- GID: D5/S3/Quantum/Algebra/Comparison/LineReflectionGeneration
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/LineReflectionGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Line reflections generate O(n) for even n and exactly SO(n) for odd n. -/


import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Module Submodule

/-! Reflections in lines `ℝ ∙ v`, `v ≠ 0`, of a finite-dimensional real inner product space have
determinant `(-1) ^ (n - 1)`. They generate the whole orthogonal group when the dimension `n` is
even and exactly the isometries of determinant one when `n` is odd. -/

namespace D5.S3.Quantum.Algebra.Comparison.LineReflectionGeneration

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The determinant of a composition of isometries is the product of the determinants. -/
private lemma det_mul (a b : F ≃ₗᵢ[ℝ] F) :
    LinearMap.det ((a * b).toLinearEquiv : F →ₗ[ℝ] F) =
      LinearMap.det (a.toLinearEquiv : F →ₗ[ℝ] F) *
        LinearMap.det (b.toLinearEquiv : F →ₗ[ℝ] F) :=
  LinearMap.det_comp _ _

/-- The identity isometry has determinant one. -/
private lemma det_one :
    LinearMap.det ((1 : F ≃ₗᵢ[ℝ] F).toLinearEquiv : F →ₗ[ℝ] F) = 1 :=
  LinearMap.det_id

/-- The isometry `-1` is central. -/
private lemma neg_commute (a : F ≃ₗᵢ[ℝ] F) : Commute (LinearIsometryEquiv.neg ℝ) a := by
  ext x
  simp

/-- The isometry `-1` is an involution. -/
private lemma neg_mul_neg : LinearIsometryEquiv.neg ℝ * LinearIsometryEquiv.neg ℝ =
    (1 : F ≃ₗᵢ[ℝ] F) := by
  ext x
  simp

/-- A reflection in the hyperplane orthogonal to a nonzero vector has determinant `-1`. -/
private lemma det_reflection_span [FiniteDimensional ℝ F] {v : F} (hv : v ≠ 0) :
    LinearMap.det ((ℝ ∙ v)ᗮ.reflection.toLinearEquiv : F →ₗ[ℝ] F) = -1 := by
  rw [det_reflection, orthogonal_orthogonal, finrank_span_singleton hv, pow_one]

/-- A product of hyperplane reflections equals `(-1) ^ k` times a product of line reflections,
where `(-1) ^ k` is also its determinant: the reflection in `(ℝ ∙ v)ᗮ` is `-1` times the
reflection in `ℝ ∙ v`, and the reflection in `(ℝ ∙ 0)ᗮ` is the identity. -/
private lemma exists_neg_pow_mul [FiniteDimensional ℝ F] (l : List F) :
    ∃ (k : ℕ) (h : F ≃ₗᵢ[ℝ] F),
      h ∈ Subgroup.closure {ρ : F ≃ₗᵢ[ℝ] F | ∃ v : F, v ≠ 0 ∧ ρ = (ℝ ∙ v).reflection} ∧
      (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod = LinearIsometryEquiv.neg ℝ ^ k * h ∧
      LinearMap.det (((l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearEquiv :
        F →ₗ[ℝ] F) = (-1) ^ k := by
  induction l with
  | nil =>
    exact ⟨0, 1, Subgroup.one_mem _, by simp,
      by rw [List.map_nil, List.prod_nil, det_one, pow_zero]⟩
  | cons v l ih =>
    obtain ⟨k, h, hh, hprod, hdet⟩ := ih
    rw [List.map_cons, List.prod_cons]
    by_cases hv : v = 0
    · subst hv
      have h0 : (ℝ ∙ (0 : F))ᗮ.reflection = 1 := by
        ext x
        exact reflection_mem_subspace_eq_self
          (mem_orthogonal_singleton_iff_inner_right.mpr (inner_zero_left _))
      exact ⟨k, h, hh, by rw [h0, one_mul, hprod], by rw [h0, one_mul, hdet]⟩
    · have hσ : (ℝ ∙ v)ᗮ.reflection =
          LinearIsometryEquiv.neg ℝ * (ℝ ∙ v).reflection := reflection_orthogonal _
      refine ⟨k + 1, (ℝ ∙ v).reflection * h,
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨v, hv, rfl⟩) hh, ?_, ?_⟩
      · rw [hprod, hσ]
        simp only [pow_succ', mul_assoc]
        rw [← mul_assoc (ℝ ∙ v).reflection, ← ((neg_commute _).pow_left k).eq, mul_assoc]
      · rw [det_mul, det_reflection_span hv, hdet]
        ring

/-- In odd dimension every line reflection has determinant one, hence so does every element of
the group they generate. -/
private lemma det_eq_one_of_mem [FiniteDimensional ℝ F] (hn : ¬ Even (finrank ℝ F))
    {g : F ≃ₗᵢ[ℝ] F}
    (hg : g ∈ Subgroup.closure {ρ : F ≃ₗᵢ[ℝ] F | ∃ v : F, v ≠ 0 ∧ ρ = (ℝ ∙ v).reflection}) :
    LinearMap.det (g.toLinearEquiv : F →ₗ[ℝ] F) = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hn
    have hsum := finrank_add_finrank_orthogonal (ℝ ∙ v)
    rw [finrank_span_singleton hv] at hsum
    have hperp : finrank ℝ (ℝ ∙ v)ᗮ = 2 * m := by omega
    rw [det_reflection, hperp]
    exact (even_two_mul m).neg_one_pow
  | one => exact det_one
  | mul x y _ _ hx hy => rw [det_mul, hx, hy, one_mul]
  | inv x _ hx =>
    have h := det_mul x⁻¹ x
    rw [inv_mul_cancel, hx, mul_one] at h
    rw [← h, det_one]

/-- In a finite-dimensional real inner product space, an isometry is a product of reflections in
lines `ℝ ∙ v` with `v ≠ 0` if and only if the dimension is even or its determinant is one. -/
theorem mem_closure_lineReflections_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (g : F ≃ₗᵢ[ℝ] F) :
    g ∈ Subgroup.closure {ρ : F ≃ₗᵢ[ℝ] F | ∃ v : F, v ≠ 0 ∧ ρ = (ℝ ∙ v).reflection} ↔
      Even (Module.finrank ℝ F) ∨ LinearMap.det (g.toLinearEquiv : F →ₗ[ℝ] F) = 1 := by
  have key : ∀ g : F ≃ₗᵢ[ℝ] F, ∃ (k : ℕ) (h : F ≃ₗᵢ[ℝ] F),
      h ∈ Subgroup.closure {ρ : F ≃ₗᵢ[ℝ] F | ∃ v : F, v ≠ 0 ∧ ρ = (ℝ ∙ v).reflection} ∧
      g = LinearIsometryEquiv.neg ℝ ^ k * h ∧
      LinearMap.det (g.toLinearEquiv : F →ₗ[ℝ] F) = (-1) ^ k := by
    intro g
    obtain ⟨l, -, rfl⟩ := g.reflections_generate_dim
    exact exists_neg_pow_mul l
  have mem_of_det : ∀ g : F ≃ₗᵢ[ℝ] F, LinearMap.det (g.toLinearEquiv : F →ₗ[ℝ] F) = 1 →
      g ∈ Subgroup.closure {ρ : F ≃ₗᵢ[ℝ] F | ∃ v : F, v ≠ 0 ∧ ρ = (ℝ ∙ v).reflection} := by
    intro g hg
    obtain ⟨k, h, hh, rfl, hdet⟩ := key g
    rw [hg] at hdet
    obtain ⟨j, rfl⟩ := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hdet.symm
    rwa [← two_mul, pow_mul, sq, neg_mul_neg, one_pow, one_mul]
  constructor
  · intro hg
    by_cases hn : Even (finrank ℝ F)
    · exact Or.inl hn
    · exact Or.inr (det_eq_one_of_mem hn hg)
  · rintro (hn | hg)
    · obtain ⟨k, h, hh, rfl, -⟩ := key g
      refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (mem_of_det _ ?_) _) hh
      rw [← reflection_bot, det_reflection, bot_orthogonal_eq_top, finrank_top]
      exact hn.neg_one_pow
    · exact mem_of_det g hg

end D5.S3.Quantum.Algebra.Comparison.LineReflectionGeneration
