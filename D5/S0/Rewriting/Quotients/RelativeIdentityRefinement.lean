/- GID: D5/S0/Rewriting/Quotients/RelativeIdentityRefinement
   generality: G
   mirror-B: D5/B/S0/Rewriting/Quotients/RelativeIdentityRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement induces one surjection between relative-identity quotients. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-16):
   * Exact pinned-Mathlib hit: `Setoid.map_of_le` constructs the map between
     quotients induced by an inclusion of setoids; it is applied below.
   * Exact pinned-Mathlib hit: `Setoid.lift_unique` is the quotient universal
     property's uniqueness theorem; it is applied below.
   * Two local smart-search queries returned no declaration-name hit for the
     combined antitonicity, surjectivity, and uniqueness statement.
   * D5 searches for quotient refinement, relation inclusion, and induced
     surjections found adjacent quotient results but no equivalent theorem.
-/

namespace D5.S0.Rewriting.Quotients.RelativeIdentityRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If a coarse readout factors through a fine readout, fine relative identity
implies coarse relative identity. The identity on representatives therefore
descends uniquely to a surjection from the fine quotient to the coarse one. -/
theorem relative_identity_refinement
    {X Fine Coarse : Type*} (fine : X → Fine) (coarse : X → Coarse)
    (forget : Fine → Coarse) (hfactor : coarse = forget ∘ fine) :
    (Setoid.ker fine ≤ Setoid.ker coarse) ∧
      ∃! descend : Quotient (Setoid.ker fine) → Quotient (Setoid.ker coarse),
        Function.Surjective descend ∧
          ∀ x, descend (Quotient.mk'' x) = Quotient.mk'' x := by
  have hle : Setoid.ker fine ≤ Setoid.ker coarse := by
    intro x y hxy
    change coarse x = coarse y
    rw [hfactor]
    exact congrArg forget hxy
  refine ⟨hle, ?_⟩
  let descend : Quotient (Setoid.ker fine) → Quotient (Setoid.ker coarse) :=
    Setoid.map_of_le hle
  refine ⟨descend, ?_, ?_⟩
  · constructor
    · intro value
      refine Quotient.inductionOn' value fun x => ?_
      exact ⟨Quotient.mk'' x, rfl⟩
    · intro x
      rfl
  · intro candidate hcandidate
    have hlift :
        Quotient.lift
            (fun x : X => (Quotient.mk'' x : Quotient (Setoid.ker coarse)))
            (fun _ _ hxy => Quotient.sound' (hle hxy)) =
          candidate := by
      apply Setoid.lift_unique
      funext x
      exact (hcandidate.2 x).symm
    calc
      candidate =
          Quotient.lift
            (fun x : X => (Quotient.mk'' x : Quotient (Setoid.ker coarse)))
            (fun _ _ hxy => Quotient.sound' (hle hxy)) := hlift.symm
      _ = descend := by
        funext value
        refine Quotient.inductionOn' value fun x => ?_
        rfl

#print axioms relative_identity_refinement

end D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
