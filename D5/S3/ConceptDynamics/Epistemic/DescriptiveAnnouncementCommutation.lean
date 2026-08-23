/- GID: D5/S3/ConceptDynamics/Epistemic/DescriptiveAnnouncementCommutation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/DescriptiveAnnouncementCommutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditioning by two descriptive announcements commutes. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-22):
   * Current-tree searches for descriptive announcements, announcement
     conditioning, and the two-announcement operator equality found no exact
     family primitive or theorem.
   * Pinned Mathlib's `Set.inter_right_comm` is the exact set identity needed
     after unfolding the source conditioning semantics, and is applied directly.
   * Loogle found `Set.inter_right_comm`; no separate LeanSearch exact hit was
     needed after the pinned declaration closed the theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.DescriptiveAnnouncementCommutation

/-- A descriptive announcement restricts the currently admitted states to
those satisfying the announcement predicate. -/
def descriptiveCondition {State : Type*}
    (announcement admitted : Set State) : Set State :=
  admitted ∩ announcement

/-- Conditioning successively by two descriptive announcements commutes. The
public equality is between the canonical conditioning operators themselves. -/
theorem descriptive_announcement_commutation {State : Type*}
    (P Q : Set State) :
    (descriptiveCondition P ∘ descriptiveCondition Q) =
      (descriptiveCondition Q ∘ descriptiveCondition P) := by
  funext admitted
  change admitted ∩ Q ∩ P = admitted ∩ P ∩ Q
  exact Set.inter_right_comm admitted Q P

/-- A concrete inhabitant exercises the source conditioning operation. -/
example :
    descriptiveCondition ({true} : Set Bool) Set.univ = {true} := by
  simp [descriptiveCondition]

#print axioms descriptive_announcement_commutation

end D5.S3.ConceptDynamics.Epistemic.DescriptiveAnnouncementCommutation
