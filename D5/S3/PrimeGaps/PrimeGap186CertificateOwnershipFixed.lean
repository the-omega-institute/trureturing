/- GID: D5/S3/PrimeGaps/PrimeGap186CertificateOwnershipFixed
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonically address the finite physical-certificate obligations without inventing unsupported source ownership. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

namespace D5.S3.PrimeGaps.PrimeGap186CertificateOwnershipFixed

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

inductive PhysicalObligationClass
  | outer | inner | scalar
  deriving DecidableEq, Repr

inductive PhysicalObligationAddress
  | outer (index : Fin 104)
  | inner (index : Fin 45)
  | scalar (index : Fin 3)
  deriving DecidableEq, Repr

instance : Fintype PhysicalObligationAddress := Fintype.ofFinite _

def PhysicalObligationAddress.obligationClass : PhysicalObligationAddress → PhysicalObligationClass
  | .outer _ => .outer
  | .inner _ => .inner
  | .scalar _ => .scalar

theorem card_physicalObligationAddress : Fintype.card PhysicalObligationAddress = 152 := by
  native_decide

structure PhysicalOwnershipRelation where
  owns : PhysicalObligationAddress → PhysicalSourceGroup → Prop

def PhysicalOwnershipRelation.Functional (R : PhysicalOwnershipRelation) : Prop :=
  ∀ a g₁ g₂, R.owns a g₁ → R.owns a g₂ → g₁ = g₂

def PhysicalOwnershipRelation.TotalOnNonscalar (R : PhysicalOwnershipRelation) : Prop :=
  ∀ a, a.obligationClass ≠ .scalar → ∃ g, R.owns a g

def ValidatedPhysicalOwnership (R : PhysicalOwnershipRelation) : Prop :=
  R.Functional ∧ R.TotalOnNonscalar

theorem existsUnique_owner_of_validated
    (R : PhysicalOwnershipRelation) (hR : ValidatedPhysicalOwnership R)
    (a : PhysicalObligationAddress) (ha : a.obligationClass ≠ .scalar) :
    ∃! g, R.owns a g := by
  obtain ⟨g, hg⟩ := hR.2 a ha
  refine ⟨g, hg, ?_⟩
  intro y hy
  exact hR.1 a y g hy hg

#print axioms PhysicalObligationAddress
#print axioms card_physicalObligationAddress
#print axioms PhysicalOwnershipRelation
#print axioms existsUnique_owner_of_validated

end D5.S3.PrimeGaps.PrimeGap186CertificateOwnershipFixed
