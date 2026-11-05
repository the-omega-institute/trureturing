/- GID: D5/S1/Dynamics/Shadowing/PengTwoFaceBridge
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/PengTwoFaceBridge
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Explicit two-face path-lifting bridges for Peng's shadowing construction. -/

import D5.S1.Dynamics.Shadowing.CoherentFollowerCover

open Set Function Filter Topology

namespace D5.S1.Dynamics.Shadowing.CoherentFollower

universe u v w

variable {I : Type u} {A : I → Type v} [∀ i, TopologicalSpace (A i)]
variable (S : LanguageSystem A)

/-!
  The concrete two-coordinate face used in Peng's finite-face question.

  The `image_eq` field of `S` is the explicit whole-word compatibility
  premise. This corollary only specializes the general lifting theorem; it
  does not construct that premise for a proposed shadowing extension.
-/
theorem two_face_restrictPath_surjective [DecidableEq I] {α β : I} (hαβ : α ≠ β) :
    Surjective (S.restrictPath (F := ({β} : Finset I))
      (G := ({α, β} : Finset I)) (by
        intro i hi
        have hi' : i = β := Finset.mem_singleton.mp hi
        subst i
        simp)) := by
  exact S.restrictPath_surjective _

/-!
  The corresponding concrete prefix-lifting statement. As above, the
  whole-word compatibility supplied by `LanguageSystem.image_eq` remains an
  explicit premise through `S`; this is only the two-face specialization.
-/
theorem two_face_every_prefix_lifts [DecidableEq I] [∀ i, Finite (A i)]
    {α β : I} (hαβ : α ≠ β) :
    ∀ p ∈ graphLanguage
        (S.Edge (F := ({β} : Finset I))) id, ∀ m,
      PrefixLift (S.Edge (F := ({α, β} : Finset I)))
        (S.restrictVertex (F := ({β} : Finset I))
          (G := ({α, β} : Finset I)) (by
            intro i hi
            have hi' : i = β := Finset.mem_singleton.mp hi
            subst i
            simp)) p m := by
  intro p hp m
  exact (S.every_prefix_lifts (h := by
    intro i hi
    have hi' : i = β := Finset.mem_singleton.mp hi
    subst i
    simp)) p hp m

end D5.S1.Dynamics.Shadowing.CoherentFollower

#print axioms D5.S1.Dynamics.Shadowing.CoherentFollower.two_face_restrictPath_surjective
#print axioms D5.S1.Dynamics.Shadowing.CoherentFollower.two_face_every_prefix_lifts
