/- GID: D5/S3/Analytic/Convexity/LexicographicFlagRealization
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/LexicographicFlagRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite feasibility admits an orthonormal lexicographic list bounded by input rank. -/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

noncomputable section

open scoped InnerProductSpace
open Module Set

namespace D5.S3.Analytic.Convexity.LexicographicFlagRealization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {I : Type*}

/-- Every finite set of rows has one strictly positive input. -/
def FiniteFeasible (a : I → V) : Prop :=
  ∀ F : Finset I, ∃ x : V, ∀ i ∈ F, 0 < ⟪a i, x⟫_ℝ

/-- Every row has a positive first nonzero entry in the same ordered list. -/
def LexWitness (a : I → V) {r : ℕ} (v : Fin r → V) : Prop :=
  ∀ i, ∃ k, 0 < ⟪a i, v k⟫_ℝ ∧ ∀ j < k, ⟪a i, v j⟫_ℝ = 0

variable [FiniteDimensional ℝ V]

private theorem common_weak_unit (a : I → V) [Nonempty I] (h : FiniteFeasible a) :
    ∃ u : V, u ∈ Submodule.span ℝ (Set.range a) ∧ ‖u‖ = 1 ∧
      ∀ i, 0 ≤ ⟪a i, u⟫_ℝ := by
  classical
  let W := Submodule.span ℝ (Set.range a)
  let b : I → W := fun i => ⟨a i, Submodule.subset_span (Set.mem_range_self i)⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hfinite (F : Finset I) :
      (Metric.sphere (0 : W) 1 ∩ ⋂ i ∈ F, {u : W | 0 ≤ ⟪b i, u⟫_ℝ}).Nonempty := by
    obtain ⟨x, hx⟩ := h (insert i₀ F)
    let y : W := W.orthogonalProjectionOnto x
    have heval (i : I) : ⟪b i, y⟫_ℝ = ⟪a i, x⟫_ℝ :=
      W.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) x
    have hy : y ≠ 0 := by
      intro hy
      have hp := hx i₀ (Finset.mem_insert_self _ _)
      rw [← heval i₀, hy, inner_zero_right] at hp
      exact lt_irrefl _ hp
    refine ⟨NormedSpace.normalize y, ?_, ?_⟩
    · simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hy
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro i hi
      rw [NormedSpace.normalize, inner_smul_right, heval]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg y))
        (le_of_lt (hx i (Finset.mem_insert_of_mem hi)))
  obtain ⟨u, hu, hi⟩ := (isCompact_sphere (0 : W) 1).inter_iInter_nonempty
    (fun i => {u : W | 0 ≤ ⟪b i, u⟫_ℝ})
    (fun i => isClosed_le continuous_const (continuous_const.inner continuous_id)) hfinite
  refine ⟨u, u.property, ?_, ?_⟩
  · simpa using hu
  · intro i
    exact Set.mem_iInter.mp hi i

/-- A common orthonormal list in the row span settles every row, with length at most its rank. -/
theorem orthonormal_realization (a : I → V) (h : FiniteFeasible a) :
    ∃ (r : ℕ) (v : Fin r → V), r ≤ finrank ℝ (Submodule.span ℝ (Set.range a)) ∧
      Orthonormal ℝ v ∧ (∀ k, v k ∈ Submodule.span ℝ (Set.range a)) ∧ LexWitness a v := by
  classical
  suffices aux : ∀ n, ∀ (J : Type _) (b : J → V),
      finrank ℝ (Submodule.span ℝ (Set.range b)) = n → FiniteFeasible b →
      ∃ (r : ℕ) (v : Fin r → V), r ≤ n ∧ Orthonormal ℝ v ∧
        (∀ k, v k ∈ Submodule.span ℝ (Set.range b)) ∧ LexWitness b v by
    exact aux _ I a rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J b hn hb
    cases isEmpty_or_nonempty J with
    | inl hempty =>
      exact ⟨0, Fin.elim0, Nat.zero_le _, Orthonormal.of_isEmpty _,
        fun k => Fin.elim0 k, fun j => isEmptyElim j⟩
    | inr hnonempty =>
      obtain ⟨u, huW, hu, hupos⟩ := common_weak_unit b hb
      let K := {j : J // ⟪b j, u⟫_ℝ = 0}
      let c : K → V := fun j => b j.val
      let W := Submodule.span ℝ (Set.range b)
      let W' := Submodule.span ℝ (Set.range c)
      have hle : W' ≤ W := Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span (Set.mem_range_self j.val))
      have horth : W' ≤ (ℝ ∙ u)ᗮ := Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr j.property)
      have hnot : u ∉ W' := by
        intro hu'
        have hz := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (horth hu')
        have : u = 0 := inner_self_eq_zero.mp hz
        simpa [this] using hu
      have hrank : finrank ℝ W' < n := by
        rw [← hn]
        exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle (by
          intro heq
          exact hnot (heq.symm ▸ huW)))
      have hc : FiniteFeasible c := by
        intro F
        obtain ⟨x, hx⟩ := hb (F.image Subtype.val)
        exact ⟨x, fun j hj => hx j.val (Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
      obtain ⟨s, w, hs, hw, hwW, hwlex⟩ := ih _ hrank K c rfl hc
      refine ⟨s + 1, Matrix.vecCons u w, by omega, ?_, ?_, ?_⟩
      · apply orthonormal_vecCons_iff.mpr
        exact ⟨hu, fun k =>
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp (horth (hwW k)), hw⟩
      · intro k
        exact Fin.cases huW (fun j => hle (hwW j)) k
      · intro j
        by_cases hj : ⟪b j, u⟫_ℝ = 0
        · obtain ⟨k, hk, hkzero⟩ := hwlex ⟨j, hj⟩
          refine ⟨k.succ, hk, ?_⟩
          intro l hl
          refine Fin.cases ?_ (fun q hq => ?_) l hl
          · intro _
            exact hj
          · exact hkzero q (Fin.succ_lt_succ_iff.mp hq)
        · refine ⟨0, lt_of_le_of_ne (hupos j) (Ne.symm hj), ?_⟩
          intro k hk
          exact (Fin.not_lt_zero k hk).elim

end D5.S3.Analytic.Convexity.LexicographicFlagRealization
