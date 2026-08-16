/- GID: D5/S3/ResourceOrder/MinimumMeanSquareHedge
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/MinimumMeanSquareHedge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orthogonal projection is the unique minimum-mean-square hedge. -/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/- Library-search audit trail (2026-08-17):
   * Pinned Mathlib supplies the exact Pythagorean core
     `Submodule.norm_sq_eq_add_norm_sq_starProjection` and the exact
     best-approximation core `Submodule.starProjection_minimal`.
   * Repository searches found uses of both projection results, but no theorem
     combining the payoff decomposition, unique minimizer, and squared infimum.
-/

noncomputable section

namespace D5.S3.ResourceOrder.MinimumMeanSquareHedge

/-- In a finite-dimensional real Hilbert space, every attainable payoff has
the orthogonal squared-error decomposition. The projection is characterized as
the unique minimizer, and the infimum is the squared residual norm. -/
theorem minimum_mean_square_hedge
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (marketed : Submodule Real V) (claim : V) :
    (forall payoff : marketed,
      ‖claim - (payoff : V)‖ ^ 2 =
        ‖marketedᗮ.starProjection claim‖ ^ 2 +
          ‖marketed.starProjection claim - (payoff : V)‖ ^ 2) ∧
    (forall payoff : marketed,
      (forall alternative : marketed,
        ‖claim - (payoff : V)‖ ^ 2 <=
          ‖claim - (alternative : V)‖ ^ 2) ↔
        (payoff : V) = marketed.starProjection claim) ∧
    (⨅ payoff : marketed, ‖claim - (payoff : V)‖ ^ 2) =
      ‖marketedᗮ.starProjection claim‖ ^ 2 := by
  have hDecomposition : forall payoff : marketed,
      ‖claim - (payoff : V)‖ ^ 2 =
        ‖marketedᗮ.starProjection claim‖ ^ 2 +
          ‖marketed.starProjection claim - (payoff : V)‖ ^ 2 := by
    intro payoff
    have hPythagorean :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection
        (claim - (payoff : V)) marketed
    have hOrthogonalPayoff : marketedᗮ.starProjection (payoff : V) = 0 := by
      have hProjection : marketedᗮ.orthogonalProjectionOnto (payoff : V) = 0 :=
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
          (marketed.le_orthogonal_orthogonal payoff.property)
      rw [Submodule.starProjection_apply, hProjection]
      rfl
    rw [map_sub, marketed.starProjection_mem_subspace_eq_self payoff,
      map_sub, hOrthogonalPayoff, sub_zero] at hPythagorean
    simpa only [add_comm] using hPythagorean
  have hMinimizer : forall payoff : marketed,
      (forall alternative : marketed,
        ‖claim - (payoff : V)‖ ^ 2 <=
          ‖claim - (alternative : V)‖ ^ 2) ↔
        (payoff : V) = marketed.starProjection claim := by
    intro payoff
    constructor
    · intro hOptimal
      let projection : marketed := marketed.orthogonalProjectionOnto claim
      have hAtProjection := hOptimal projection
      rw [hDecomposition payoff, hDecomposition projection] at hAtProjection
      simp only [projection, Submodule.starProjection_apply, sub_self, norm_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hAtProjection
      have hSquared : ‖marketed.starProjection claim - (payoff : V)‖ ^ 2 <= 0 := by
        rw [Submodule.starProjection_apply]
        linarith
      have hNormSquared : ‖marketed.starProjection claim - (payoff : V)‖ ^ 2 = 0 :=
        le_antisymm hSquared (sq_nonneg _)
      have hNorm : ‖marketed.starProjection claim - (payoff : V)‖ = 0 :=
        sq_eq_zero_iff.mp hNormSquared
      exact (sub_eq_zero.mp (norm_eq_zero.mp hNorm)).symm
    · intro hProjection alternative
      rw [hProjection]
      have hNormMinimal :
          ‖claim - marketed.starProjection claim‖ <=
            ‖claim - (alternative : V)‖ := by
        rw [marketed.starProjection_minimal claim]
        exact ciInf_le
          ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ alternative
      nlinarith [norm_nonneg (claim - marketed.starProjection claim),
        norm_nonneg (claim - (alternative : V))]
  have hInfimum :
      (⨅ payoff : marketed, ‖claim - (payoff : V)‖ ^ 2) =
        ‖marketedᗮ.starProjection claim‖ ^ 2 := by
    apply le_antisymm
    · let projection : marketed := marketed.orthogonalProjectionOnto claim
      calc
        (⨅ payoff : marketed, ‖claim - (payoff : V)‖ ^ 2) <=
            ‖claim - (projection : V)‖ ^ 2 :=
          ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => sq_nonneg _⟩ projection
        _ = ‖marketedᗮ.starProjection claim‖ ^ 2 := by
          rw [hDecomposition projection]
          have hProjectionValue : (projection : V) = marketed.starProjection claim := by
            rfl
          rw [hProjectionValue, sub_self, norm_zero, zero_pow (by norm_num), add_zero]
    · refine le_ciInf fun payoff => ?_
      rw [hDecomposition payoff]
      exact le_add_of_nonneg_right (sq_nonneg _)
  exact ⟨hDecomposition, hMinimizer, hInfimum⟩

#print axioms minimum_mean_square_hedge

end D5.S3.ResourceOrder.MinimumMeanSquareHedge
