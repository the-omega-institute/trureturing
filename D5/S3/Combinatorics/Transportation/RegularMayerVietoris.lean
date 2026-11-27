/- GID: D5/S3/Combinatorics/Transportation/RegularMayerVietoris
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/RegularMayerVietoris
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular conical coefficients admit finite-fiber transport exactly under idempotent refinement and the two Mayer-Vietoris laws. -/

import OmegaMath.Algebra.Refinement.RegularMayerVietoris
import D5.S3.Combinatorics.Transportation.FiniteFiberTransport

/-! The regular coefficient criterion combines Goodearl--Pardo--Wehrung,
Theorem 3.2, with the exact transportation equivalence. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Transportation.RegularMayerVietoris

open Omega.Refinement Omega.Refinement.Regular
universe u v w z

/-- The full regular coefficient criterion, including empty finite carriers and
an arbitrary label type in an independent universe. -/
theorem regular_mvp_iff_finite_fiber_transport (K : Type u) [AddCommMonoid K]
    (hreg : ∀ x : K, ∃ y : K, x + y + x = x) :
    (Conical K ∧ IdempotentRefinement K ∧ ComponentSum K ∧ CommonLift K) ↔
      FiniteFiberTransport.{u,v,w,z} K := by
  have ht :=
    FiniteFiberTransport.conical_refinement_iff_finite_fiber_transport.{u,v,w,z} K
  change (Conical K ∧ BinaryRefinement K) ↔ FiniteFiberTransport.{u,v,w,z} K at ht
  constructor
  · rintro ⟨hc, hir, hs, hl⟩
    exact ht.mp ⟨hc, refinement_of_mayer_vietoris hreg hir hs hl⟩
  · intro h
    obtain ⟨hc, hr⟩ := ht.mpr h
    exact ⟨hc, (refinement_iff_mayer_vietoris hreg).mp hr⟩

end D5.S3.Combinatorics.Transportation.RegularMayerVietoris
