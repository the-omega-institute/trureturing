/- GID: D5/S3/ConceptDynamics/Policy/CocyclePolicySeparation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Policy/CocyclePolicySeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cocycle composition and hidden accounting do not select a unique legal action. -/

import D5.S1.Dynamics.JumpCocycle
import D5.S3.ConceptDynamics.Policy.DiscretionaryOutcomeNonuniqueness

/- Library-search audit trail (2026-08-27):
   * Exact repository hit `D5.S1.Dynamics.JumpCocycle.jump_cocycle` supplies the
     visible agreement, endpoint/cocycle equivalence, and explicit inconsistency
     residual for selected hidden jumps.
   * Exact repository hit
     `D5.S3.ConceptDynamics.Policy.DiscretionaryOutcomeNonuniqueness.
     discretionary_outcome_nonuniqueness` supplies the policy-side failure of
     unique selection from two permitted outcomes.
   * Pinned Mathlib search for a theorem combining cocycle accounting with policy
     choice found no exact declaration; only generic additive and uniqueness
     primitives are used by the imported theorems.
   * Body-shape primitive search for cocycle and policy constructions found the
     declarations above; no new `def` or `abbrev` is introduced here.
   * Loogle and LeanSearch are unavailable on PATH in this worktree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.CocyclePolicySeparation

/-- The hidden-jump cocycle accounts for selected-action composition, while two
licensed outcomes in the same public-law fiber leave the policy choice nonunique. -/
theorem cocycle_does_not_select_policy
    {U Sigma Case PublicFact Outcome : Type*}
    [Nonempty U] [AddCommGroup Sigma]
    (projection : Sigma →+ AddCircle (1 : ℝ))
    (hProjectionSurjective : Function.Surjective projection)
    (hiddenEquiv : (∀ p : Nat.Primes, ℤ_[p.1]) ≃+ projection.ker)
    (sectionAlpha sectionBeta sectionGamma : U → Sigma)
    (jumpAlphaBeta jumpBetaGamma jumpAlphaGamma :
      U → ∀ p : Nat.Primes, ℤ_[p.1])
    (hAlphaBeta : ∀ u, sectionBeta u =
      sectionAlpha u + (hiddenEquiv (jumpAlphaBeta u) : Sigma))
    (hBetaGamma : ∀ u, sectionGamma u =
      sectionBeta u + (hiddenEquiv (jumpBetaGamma u) : Sigma))
    (publicLaw : Case → PublicFact)
    (admissible : Case → Prop)
    (permitted : Case → Outcome → Prop)
    (b : PublicFact)
    (multipleOutcomes :
      ∃ leftOutcome rightOutcome,
        leftOutcome ≠ rightOutcome ∧
          (∃ x, admissible x ∧ publicLaw x = b ∧ permitted x leftOutcome) ∧
          ∃ x, admissible x ∧ publicLaw x = b ∧ permitted x rightOutcome) :
    ((∀ u, projection (sectionAlpha u) = projection (sectionBeta u) ∧
        projection (sectionBeta u) = projection (sectionGamma u)) ∧
      ((∀ u, sectionGamma u =
          sectionAlpha u + (hiddenEquiv (jumpAlphaGamma u) : Sigma)) ↔
        ∀ u, jumpAlphaGamma u = jumpAlphaBeta u + jumpBetaGamma u) ∧
      ((∃ u, jumpAlphaGamma u ≠ jumpAlphaBeta u + jumpBetaGamma u) →
        ∃ u, sectionGamma u ≠
          sectionAlpha u + (hiddenEquiv (jumpAlphaGamma u) : Sigma))) ∧
      ¬ ∃! outcome,
        ∃ x, admissible x ∧ publicLaw x = b ∧ permitted x outcome := by
  refine ⟨?_, ?_⟩
  · exact D5.S1.Dynamics.JumpCocycle.jump_cocycle projection
      hProjectionSurjective hiddenEquiv sectionAlpha sectionBeta sectionGamma
      jumpAlphaBeta jumpBetaGamma jumpAlphaGamma hAlphaBeta hBetaGamma
  · exact D5.S3.ConceptDynamics.Policy.DiscretionaryOutcomeNonuniqueness.discretionary_outcome_nonuniqueness
      publicLaw admissible permitted b
      multipleOutcomes

#print axioms cocycle_does_not_select_policy

end D5.S3.ConceptDynamics.Policy.CocyclePolicySeparation
