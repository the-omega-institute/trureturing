/- GID: D5/S3/Observer/AgencySelf/StrictKernelTowerNoFiniteTerminal
   generality: G
   mirror-B: D5/B/S3/Observer/AgencySelf/StrictKernelTowerNoFiniteTerminal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strictly refining interaction profiles have no finite terminal quotient. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-09-02):
   * Exact repository primitive `jointReadout` constructs the complete dependent
     interaction profile from all finite-stage profiles; it is imported rather
     than redeclared.
   * `StableObservationInverseLimit` constructs restriction maps for expanding
     operation-set quotients, while `RelativeIdentityRefinement` constructs one
     canonical quotient surjection. Neither states strict nonterminality for an
     arbitrary profile tower, so there is no exact frozen owner to bind.
   * Pinned Mathlib supplies `Quotient.sound'` and `Quotient.exact'`, which turn
     representative equality into equality-kernel evidence in both directions.
     Searches for strict kernel towers and representative-preserving quotient
     equivalences found no whole-theorem hit.
   * A bare type equivalence between two quotients need not identify their
     kernels. The public computation rule therefore exposes the source proof's
     canonical meaning: every history representative must map to itself.
   * Body-shape searches for `fun x i => q i x`, complete indexed profiles,
     strict kernel descent, and quotient representative equations found the
     imported `jointReadout` owner but no duplicate theorem. No new definition,
     abbreviation, or private lemma is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencySelf.StrictKernelTowerNoFiniteTerminal

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe uHistory uIntervention uInteraction

/-- If every finite interaction profile is strictly refined at the next stage,
no finite profile quotient is canonically equivalent to the complete-profile
quotient. At every finite stage, a pair of histories is explicitly separated
by the next legal interaction profile. -/
theorem strict_kernel_tower_no_finite_terminal
    {History : Type uHistory} {Intervention : Nat -> Type uIntervention}
    {Interaction : Type uInteraction}
    (interactionProfile : forall level,
      History -> Intervention level -> PMF Interaction)
    (strictDescent : forall level,
      Setoid.ker (interactionProfile (level + 1)) <
        Setoid.ker (interactionProfile level)) :
    (forall level,
      Not (exists equivalence :
          Equiv
            (Quotient (Setoid.ker (interactionProfile level)))
            (Quotient (Setoid.ker (jointReadout interactionProfile))),
        forall history,
          equivalence (Quotient.mk'' history) = Quotient.mk'' history)) /\
      (forall level, exists left right : History,
        interactionProfile level left = interactionProfile level right /\
          Ne
            (interactionProfile (level + 1) left)
            (interactionProfile (level + 1) right)) := by
  constructor
  · intro level
    rintro ⟨equivalence, preservesRepresentatives⟩
    apply (strictDescent level).2
    intro left right sameFinite
    have sameFiniteClass :
        (Quotient.mk'' left : Quotient (Setoid.ker (interactionProfile level))) =
          Quotient.mk'' right :=
      Quotient.sound' sameFinite
    have sameFullClass :
        (Quotient.mk'' left :
            Quotient (Setoid.ker (jointReadout interactionProfile))) =
          Quotient.mk'' right := by
      rw [← preservesRepresentatives left, ← preservesRepresentatives right]
      exact congrArg equivalence sameFiniteClass
    have sameFull :
        Setoid.ker (jointReadout interactionProfile) left right :=
      Quotient.exact' sameFullClass
    exact congrFun sameFull (level + 1)
  · intro level
    by_contra noSeparatingPair
    apply (strictDescent level).2
    intro left right sameFinite
    by_contra separatedNext
    exact noSeparatingPair ⟨left, right, sameFinite, separatedNext⟩

#print axioms strict_kernel_tower_no_finite_terminal

end D5.S3.Observer.AgencySelf.StrictKernelTowerNoFiniteTerminal
