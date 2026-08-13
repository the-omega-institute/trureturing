/- GID: D5/S1/Solenoid/AdditiveCocycleTransport
   generality: G
   mirror-B: D5/B/S1/Solenoid/AdditiveCocycleTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Homomorphic images turn multiplicative cocycle identities into additive ones. -/

import Mathlib.Algebra.Group.TypeTags.Hom

namespace D5.S1.Solenoid.AdditiveCocycleTransport

/-- A multiplicative cocycle identity becomes additive after applying a
homomorphism into the multiplicative type tag of an additive monoid. -/
theorem map_cocycle_to_additive
    {G A : Type*} [Monoid G] [AddMonoid A]
    (f : G →* Multiplicative A)
    {kAlphaGamma kAlphaBeta kBetaGamma : G}
    (hCocycle : kAlphaGamma = kAlphaBeta * kBetaGamma) :
    (f kAlphaGamma).toAdd =
      (f kAlphaBeta).toAdd + (f kBetaGamma).toAdd := by
  rw [hCocycle, map_mul]
  rfl

end D5.S1.Solenoid.AdditiveCocycleTransport
