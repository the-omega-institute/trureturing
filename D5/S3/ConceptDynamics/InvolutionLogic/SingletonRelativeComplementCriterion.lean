/- GID: D5/S3/ConceptDynamics/InvolutionLogic/SingletonRelativeComplementCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InvolutionLogic/SingletonRelativeComplementCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Singleton relative complements characterize two-point ambient sets. -/

import D5.S3.ConceptDynamics.InvolutionLogic.RelativeNegation

/- Library-search audit trail (2026-08-29):
   * Repository name and body-shape searches found the global
     `AtomicNegationRigidity` and `InvolutiveNegation` families, but no theorem
     with this local fixed-point equivalence. Those families require a
     complement selector at every point and are not exact owners of this claim.
   * Pinned Mathlib searches for singleton set difference, complement, and
     two-point criteria found general set-difference lemmas, but no exact
     existential equivalence. The proof below uses only set membership and
     extensionality on the source's ambient carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InvolutionLogic.SingletonRelativeComplementCriterion

/-- Removing `t` from an ambient set leaves one distinct point exactly when
the ambient set consists of those two points. -/
theorem singleton_relative_complement_iff_two_point_universe
    {X : Type*} (Ω : Set X) (t : X) (ht : t ∈ Ω) :
    (∃ s ∈ Ω, s ≠ t ∧ Ω \ {t} = {s}) ↔
      ∃ s ∈ Ω, s ≠ t ∧ Ω = {t, s} := by
  constructor
  · rintro ⟨s, hs, hst, hcomplement⟩
    refine ⟨s, hs, hst, ?_⟩
    ext x
    constructor
    · intro hx
      by_cases hxt : x = t
      · simp [hxt]
      · have hxComplement : x ∈ Ω \ {t} := ⟨hx, by simpa using hxt⟩
        have hxSingleton : x ∈ ({s} : Set X) := by
          rw [← hcomplement]
          exact hxComplement
        have hxs : x = s := by simpa using hxSingleton
        simp [hxs]
    · intro hx
      have hxCases : x = t ∨ x = s := by simpa using hx
      exact hxCases.elim (fun hxt => hxt ▸ ht) (fun hxs => hxs ▸ hs)
  · rintro ⟨s, hs, hst, hpair⟩
    refine ⟨s, hs, hst, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hxt⟩
      have hxCases : x = t ∨ x = s := by
        rw [hpair] at hx
        simpa using hx
      have xNeT : x ≠ t := by simpa using hxt
      have hxs : x = s := hxCases.resolve_left xNeT
      simp [hxs]
    · intro hxs
      have hxs' : x = s := by simpa using hxs
      subst x
      exact ⟨hs, by simpa using hst⟩

#print axioms singleton_relative_complement_iff_two_point_universe

end D5.S3.ConceptDynamics.InvolutionLogic.SingletonRelativeComplementCriterion
