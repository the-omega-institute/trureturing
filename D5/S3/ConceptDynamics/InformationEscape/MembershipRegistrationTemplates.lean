/- GID: D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MembershipRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Anchored membership and nonmembership share one membership readout with independent readout and anchor sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrationTemplates

open LeanInformationAudit

/-- Membership is an ADMIT readout; the tested element is a separate ANCHOR. -/
abbrev membershipSignature (X : Type) : PrimitiveSignature X where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .admit
  readoutAxisNotAnchor := by simp
  AnchorIndex := Unit
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def membershipRealization {X : Type} (s : Set X) [DecidablePred (· ∈ s)] (a : X) :
    PrimitiveRealization (membershipSignature X) where
  readout := fun _ x => decide (x ∈ s)
  anchor := fun _ => a

/-- The polarity selects membership or nonmembership at the supplied anchor. -/
def membershipArena (A : Arena) (positive : Bool) : PrimitiveLawArena where
  toArena := A
  signature := membershipSignature A.State
  Law r := if positive then r.readout () (r.anchor ()) = true
    else r.readout () (r.anchor ()) = false

theorem membershipLegacy (A : Arena) (positive : Bool) (s : Set A.State)
    [decMem : DecidablePred (· ∈ s)] (a : A.State) :
    LegacyPrimitiveRealization (membershipArena A positive)
      (if positive then a ∈ s else a ∉ s) (@membershipRealization A.State s decMem a) := by
  constructor
  cases positive <;> dsimp [membershipArena, membershipRealization] <;> simp

/-- Distinct states let the anchor vary while the membership readout stays fixed. -/
theorem membership_sensitivity (A : Arena) (positive : Bool)
    (a b : A.State) (hne : a ≠ b) : FiniteSlotSensitivity (membershipArena A positive) := by
  classical
  constructor
  · intro i
    cases i
    refine ⟨membershipRealization {_x | positive = true} a,
      membershipRealization {_x | positive = false} a, ?_, ?_, ?_⟩
    · intro j hj; cases j; exact (hj rfl).elim
    · intro j; rfl
    · cases positive <;> dsimp [membershipArena, membershipRealization] <;> simp
  · intro i
    cases i
    refine ⟨membershipRealization {x | if positive then x = a else x ≠ a} a,
      membershipRealization {x | if positive then x = a else x ≠ a} b, ?_, ?_, ?_⟩
    · intro j; rfl
    · intro j hj; cases j; exact (hj rfl).elim
    · cases positive <;> dsimp [membershipArena, membershipRealization] <;> simp [Ne.symm hne]

#print axioms membershipLegacy
#print axioms membership_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrationTemplates
