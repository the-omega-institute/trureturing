/- GID: D5/S1/Dynamics/JumpCocycle
   generality: I
   mirror-B: D5/B/S1/Dynamics/JumpCocycle
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Hidden-fiber jump legality is exactly cocycle consistency. -/

import D5.S1.Phase.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace D5.S1.Dynamics.JumpCocycle

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Over a nonempty domain and a surjective visible projection, a candidate
hidden-fiber jump from the first local lift to the third is legal exactly when
it is the pointwise composite of the two intervening jumps. All three lifts
have the same visible projection, and any inconsistent candidate leaves a
residual endpoint mismatch. -/
theorem jump_cocycle
    {U Sigma : Type*} [Nonempty U] [AddCommGroup Sigma]
    (projection : Sigma →+ AddCircle (1 : ℝ))
    (_hProjectionSurjective : Function.Surjective projection)
    (hiddenEquiv : (∀ p : Nat.Primes, ℤ_[p.1]) ≃+ projection.ker)
    (sectionAlpha sectionBeta sectionGamma : U → Sigma)
    (jumpAlphaBeta jumpBetaGamma jumpAlphaGamma :
      U → ∀ p : Nat.Primes, ℤ_[p.1])
    (hAlphaBeta : ∀ u, sectionBeta u =
      sectionAlpha u + (hiddenEquiv (jumpAlphaBeta u) : Sigma))
    (hBetaGamma : ∀ u, sectionGamma u =
      sectionBeta u + (hiddenEquiv (jumpBetaGamma u) : Sigma)) :
    (∀ u, projection (sectionAlpha u) = projection (sectionBeta u) ∧
      projection (sectionBeta u) = projection (sectionGamma u)) ∧
    ((∀ u, sectionGamma u =
        sectionAlpha u + (hiddenEquiv (jumpAlphaGamma u) : Sigma)) ↔
      ∀ u, jumpAlphaGamma u = jumpAlphaBeta u + jumpBetaGamma u) ∧
    ((∃ u, jumpAlphaGamma u ≠ jumpAlphaBeta u + jumpBetaGamma u) →
      ∃ u, sectionGamma u ≠
        sectionAlpha u + (hiddenEquiv (jumpAlphaGamma u) : Sigma)) := by
  have hVisible : ∀ u,
      projection (sectionAlpha u) = projection (sectionBeta u) ∧
        projection (sectionBeta u) = projection (sectionGamma u) := by
    intro u
    constructor
    · rw [hAlphaBeta u, map_add]
      rw [(hiddenEquiv (jumpAlphaBeta u)).property, add_zero]
    · rw [hBetaGamma u, map_add]
      rw [(hiddenEquiv (jumpBetaGamma u)).property, add_zero]
  have hPointwise : ∀ u,
      (sectionGamma u =
          sectionAlpha u + (hiddenEquiv (jumpAlphaGamma u) : Sigma) ↔
        jumpAlphaGamma u = jumpAlphaBeta u + jumpBetaGamma u) := by
    intro u
    constructor
    · intro hEndpoint
      apply hiddenEquiv.injective
      apply Subtype.ext
      apply add_left_cancel (a := sectionAlpha u)
      calc
        sectionAlpha u + (hiddenEquiv (jumpAlphaGamma u) : Sigma) =
            sectionGamma u := hEndpoint.symm
        _ = sectionBeta u + (hiddenEquiv (jumpBetaGamma u) : Sigma) :=
          hBetaGamma u
        _ = (sectionAlpha u + (hiddenEquiv (jumpAlphaBeta u) : Sigma)) +
            (hiddenEquiv (jumpBetaGamma u) : Sigma) := by rw [hAlphaBeta u]
        _ = sectionAlpha u +
            ((hiddenEquiv (jumpAlphaBeta u) : Sigma) +
              (hiddenEquiv (jumpBetaGamma u) : Sigma)) := by rw [add_assoc]
        _ = sectionAlpha u +
            (hiddenEquiv (jumpAlphaBeta u + jumpBetaGamma u) : Sigma) := by
          rw [hiddenEquiv.map_add]
          rfl
    · intro hCocycle
      calc
        sectionGamma u =
            sectionBeta u + (hiddenEquiv (jumpBetaGamma u) : Sigma) :=
          hBetaGamma u
        _ = (sectionAlpha u + (hiddenEquiv (jumpAlphaBeta u) : Sigma)) +
            (hiddenEquiv (jumpBetaGamma u) : Sigma) := by rw [hAlphaBeta u]
        _ = sectionAlpha u +
            ((hiddenEquiv (jumpAlphaBeta u) : Sigma) +
              (hiddenEquiv (jumpBetaGamma u) : Sigma)) := by rw [add_assoc]
        _ = sectionAlpha u +
            (hiddenEquiv (jumpAlphaBeta u + jumpBetaGamma u) : Sigma) := by
          rw [hiddenEquiv.map_add]
          rfl
        _ = sectionAlpha u + (hiddenEquiv (jumpAlphaGamma u) : Sigma) := by
          rw [hCocycle]
  refine ⟨hVisible, ?_, ?_⟩
  · constructor
    · intro hEndpoint u
      exact (hPointwise u).mp (hEndpoint u)
    · intro hCocycle u
      exact (hPointwise u).mpr (hCocycle u)
  · rintro ⟨u, hInconsistent⟩
    refine ⟨u, ?_⟩
    intro hEndpoint
    exact hInconsistent ((hPointwise u).mp hEndpoint)

end D5.S1.Dynamics.JumpCocycle
