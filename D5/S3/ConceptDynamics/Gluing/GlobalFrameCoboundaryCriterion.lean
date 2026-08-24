/- GID: D5/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A global unit frame exists exactly when transition data is a coboundary. -/

import Mathlib.Algebra.Group.Basic

/- Library-search audit trail (2026-08-24):
   * Pinned Mathlib searches for global frames, transition cocycles, compatible
     unit coefficients, and coboundaries found no exact combined theorem.
   * `Geometry.Manifold.VectorBundle.LocalFrame` provides `IsLocalFrameOn`,
     trivialization-induced `basisAt`, and `localFrame`, but no global-frame
     criterion in terms of transition data.
   * The repository's `ThroatTransitionCocycle` is an instance-specific
     additive lift-difference theorem and does not supply this multiplicative
     descent criterion.
   * The proof below uses only the standard group inverse and cancellation
     simplifications from the imported Mathlib group API. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.GlobalFrameCoboundaryCriterion

/-- For unit-valued transition data on cover overlaps, a global nonvanishing
frame is represented by unit-valued local coefficients compatible with every
transition. Such coefficients exist exactly when the transition data is a
coboundary of a family of local units. -/
theorem global_frame_iff_transition_coboundary
    {Index Base UnitGroup : Type*} [Group UnitGroup]
    (overlap : Index -> Index -> Base -> Prop)
    (transition : Index -> Index -> Base -> UnitGroup) :
    (∃ globalFrameCoefficients : Index -> Base -> UnitGroup,
        ∀ i j x, overlap i j x ->
          globalFrameCoefficients i x =
            transition i j x * globalFrameCoefficients j x) ↔
      ∃ localUnit : Index -> Base -> UnitGroup,
        ∀ i j x, overlap i j x ->
          transition i j x = (localUnit i x)⁻¹ * localUnit j x := by
  constructor
  · rintro ⟨globalFrameCoefficients, hCompatible⟩
    refine ⟨fun i x => (globalFrameCoefficients i x)⁻¹, ?_⟩
    intro i j x hx
    rw [inv_inv]
    have h := congrArg (fun unit => unit * (globalFrameCoefficients j x)⁻¹)
      (hCompatible i j x hx)
    simpa [mul_assoc] using h.symm
  · rintro ⟨localUnit, hCoboundary⟩
    refine ⟨fun i x => (localUnit i x)⁻¹, ?_⟩
    intro i j x hx
    rw [hCoboundary i j x hx]
    simp [mul_assoc]

#print axioms global_frame_iff_transition_coboundary

end D5.S3.ConceptDynamics.Gluing.GlobalFrameCoboundaryCriterion
