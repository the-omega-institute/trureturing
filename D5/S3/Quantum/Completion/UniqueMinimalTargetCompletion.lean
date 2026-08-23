/- GID: D5/S3/Quantum/Completion/UniqueMinimalTargetCompletion
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/UniqueMinimalTargetCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A projection residual generates the unique minimal closed target completion. -/

import D5.S3.Quantum.Completion.RelativeQuotientDecomposition
import Mathlib.LinearAlgebra.Isomorphisms

/- Library-search audit trail (2026-08-23):
   * Repository search found no theorem packaging the unique minimal completion
     and its relative quotient dimension.
   * Repository search found `RelativeQuotientDecomposition`, whose canonical
     relative quotient construction fixes the quotient carrier used below.
   * Pinned-Mathlib search found `Submodule.sub_starProjection_mem_orthogonal`,
     `Submodule.isClosed_sup_finiteDimensional`,
     `LinearMap.quotientInfEquivSupQuotient`, and
     `finrank_span_singleton`. They are directly applied below. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Completion.UniqueMinimalTargetCompletion

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- For a closed subspace `M` and target `x`, the orthogonal-projection residual
generates a line. Its sum with `M` is the least closed subspace containing both
`M` and `x`; when the residual is nonzero, the relative quotient has dimension
one. -/
theorem unique_minimal_target_completion (M : ClosedSubmodule 𝕜 E) (x : E) :
    let r := x - M.toSubmodule.starProjection x
    let residualLine := 𝕜 ∙ r
    let completion : ClosedSubmodule 𝕜 E :=
      { toSubmodule := M.toSubmodule ⊔ residualLine
        isClosed' := by
          exact Submodule.isClosed_sup_finiteDimensional
            M.toSubmodule residualLine M.isClosed }
    Disjoint M.toSubmodule residualLine ∧
      IsLeast
        {N : ClosedSubmodule 𝕜 E | M ≤ N ∧ x ∈ N}
        completion ∧
      (r ≠ 0 →
        Module.finrank 𝕜
          (completion.toSubmodule ⧸
            M.toSubmodule.comap completion.toSubmodule.subtype) = 1) := by
  dsimp only
  let r := x - M.toSubmodule.starProjection x
  let residualLine := 𝕜 ∙ r
  let completion : ClosedSubmodule 𝕜 E :=
    { toSubmodule := M.toSubmodule ⊔ residualLine
      isClosed' := by
        exact Submodule.isClosed_sup_finiteDimensional
          M.toSubmodule residualLine M.isClosed }
  have hr_orthogonal : r ∈ M.toSubmoduleᗮ := by
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hline_orthogonal : residualLine ≤ M.toSubmoduleᗮ := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hr_orthogonal
  have hdisjoint : Disjoint M.toSubmodule residualLine :=
    M.toSubmodule.orthogonal_disjoint.mono_right hline_orthogonal
  refine ⟨hdisjoint, ?_, ?_⟩
  · constructor
    · constructor
      · intro y hy
        change y ∈ M.toSubmodule ⊔ residualLine
        exact (le_sup_left : M.toSubmodule ≤ M.toSubmodule ⊔ residualLine) hy
      · change x ∈ M.toSubmodule ⊔ residualLine
        rw [Submodule.mem_sup]
        refine ⟨M.toSubmodule.starProjection x,
          M.toSubmodule.starProjection_apply_mem x,
          r, Submodule.mem_span_singleton_self r, ?_⟩
        calc
          M.toSubmodule.starProjection x + r =
              r + M.toSubmodule.starProjection x := add_comm _ _
          _ = x := sub_add_cancel x (M.toSubmodule.starProjection x)
    · intro N hN
      change M.toSubmodule ⊔ residualLine ≤ N.toSubmodule
      apply sup_le
      · exact hN.1
      · rw [Submodule.span_singleton_le_iff_mem]
        exact N.toSubmodule.sub_mem hN.2
          (hN.1 (M.toSubmodule.starProjection_apply_mem x))
  · intro hr
    have hline_disjoint : Disjoint residualLine M.toSubmodule := hdisjoint.symm
    have hcomap_bot :
        M.toSubmodule.comap residualLine.subtype = ⊥ :=
      Submodule.disjoint_iff_comap_eq_bot.mp hline_disjoint
    have hsecond :=
      (LinearMap.quotientInfEquivSupQuotient residualLine M.toSubmodule).finrank_eq
    change Module.finrank 𝕜
      (↥(M.toSubmodule ⊔ residualLine) ⧸
        M.toSubmodule.comap (M.toSubmodule ⊔ residualLine).subtype) = 1
    rw [sup_comm M.toSubmodule residualLine]
    rw [← hsecond]
    rw [Submodule.comap_subtype_self, hcomap_bot, top_inf_eq]
    have hquotient :=
      Submodule.finrank_quotient_add_finrank
        (⊥ : Submodule 𝕜 residualLine)
    calc
      Module.finrank 𝕜 (↥residualLine ⧸ (⊥ : Submodule 𝕜 residualLine)) =
          Module.finrank 𝕜 residualLine := by
        simpa using hquotient
      _ = 1 := finrank_span_singleton hr

example : ℝ := 0

example :
    let M : ClosedSubmodule ℝ ℝ := ⊥
    let x : ℝ := 1
    Disjoint M.toSubmodule (ℝ ∙ (x - M.toSubmodule.starProjection x)) := by
  exact
    (unique_minimal_target_completion (M := (⊥ : ClosedSubmodule ℝ ℝ)) (x := 1)).1

#print axioms unique_minimal_target_completion

end D5.S3.Quantum.Completion.UniqueMinimalTargetCompletion
