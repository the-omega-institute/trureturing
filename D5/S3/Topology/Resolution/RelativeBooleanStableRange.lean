/- GID: D5/S3/Topology/Resolution/RelativeBooleanStableRange
   generality: G
   mirror-B: D5/B/S3/Topology/Resolution/RelativeBooleanStableRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual relative Boolean lift has precisely the inverse-image stable range. -/

import D5.S1.Dynamics.StableRange
import D5.S3.Topology.Resolution.RelativeBoolean

/-!
# Stable range of the actual relative Boolean lift

The same `Space`, `point`, `projection`, and
`lift` from the topological construction are used without replacement.
The equality is proved for every natural iterate, using one source witness
for that iterate and the already proved singleton fiber over the stable core.
-/

open Set Function Topology
open D5.S1.Dynamics

namespace D5.S3.Topology.Resolution.RelativeBoolean

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The canonical lift exists for every continuous endomorphism. -/
noncomputable def stableLift (f : X → X) (hf : Continuous f) :
    Space (StableRange.core f) → Space (StableRange.core f) :=
  lift f hf (StableRange.mapsTo_core f)

/-- The projection commutes with every iterate, including the zeroth. -/
private theorem projection_iterate_lift {C : Set X} (f : X → X)
    (hf : Continuous f) (hC : MapsTo f C C) (n : ℕ) (y : Space C) :
    projection C ((lift f hf hC)^[n] y) = f^[n] (projection C y) :=
  (show Semiconj (projection C) (lift f hf hC) f from projection_lift f hf hC).iterate_right n y

/-- The stable image upstairs is exactly the full inverse image of the source
stable image. This equality itself needs only a topological space and continuity.
Compact Hausdorff and zero-dimensional core are the additional hypotheses making
this graph closure a compact zero-dimensional relative resolution. -/
theorem stable_range_lift_eq_preimage
    (f : X → X) (hf : Continuous f) :
    StableRange.core (stableLift f hf) = projection (StableRange.core f) ⁻¹' StableRange.core f := by
  ext y
  constructor
  · intro hy
    apply mem_iInter.mpr
    intro n
    obtain ⟨u, hu⟩ := mem_iInter.mp hy n
    refine ⟨projection (StableRange.core f) u, ?_⟩
    have hp := projection_iterate_lift f hf (StableRange.mapsTo_core f) n u
    change projection (StableRange.core f) ((stableLift f hf)^[n] u) =
      f^[n] (projection (StableRange.core f) u) at hp
    rw [hu] at hp
    exact hp.symm
  · intro hy
    change projection (StableRange.core f) y ∈ StableRange.core f at hy
    apply mem_iInter.mpr
    intro n
    obtain ⟨x, hx⟩ := mem_iInter.mp hy n
    let u : Space (StableRange.core f) := point (StableRange.core f) x
    have hp : projection (StableRange.core f) ((stableLift f hf)^[n] u) =
        projection (StableRange.core f) y :=
      (projection_iterate_lift f hf (StableRange.mapsTo_core f) n u).trans hx
    refine ⟨u, ?_⟩
    calc
      (stableLift f hf)^[n] u =
          point (StableRange.core f) (projection (StableRange.core f) ((stableLift f hf)^[n] u)) :=
        eq_point_of_projection_mem _ (hp.symm ▸ hy)
      _ = point (StableRange.core f) (projection (StableRange.core f) y) := congrArg _ hp
      _ = y := (eq_point_of_projection_mem y hy).symm

/-- Equivariance of the actual continuous core section, for the period supplier
and the eventual final relative-extension consumer. -/
theorem stable_lift_section (f : X → X) (hf : Continuous f) (c : StableRange.core f) :
    stableLift f hf (sectionC (StableRange.core f) c) =
      sectionC (StableRange.core f) (StableRange.restriction f c) :=
  lift_point f hf (StableRange.mapsTo_core f) c.val

/-- The constructed stable lift is continuous, has exactly the inverse-image
stable range, and acts on the actual core section as the original restriction.
The stable-image identity needs neither compactness nor separation. -/
theorem stable_lift_dynamics (f : X → X) (hf : Continuous f) :
    Continuous (stableLift f hf) ∧
      StableRange.core (stableLift f hf) =
        projection (StableRange.core f) ⁻¹' StableRange.core f ∧
      Semiconj (sectionC (StableRange.core f)) (StableRange.restriction f) (stableLift f hf) :=
  ⟨continuous_lift f hf (StableRange.mapsTo_core f),
    stable_range_lift_eq_preimage f hf, fun c => (stable_lift_section f hf c).symm⟩

end D5.S3.Topology.Resolution.RelativeBoolean
