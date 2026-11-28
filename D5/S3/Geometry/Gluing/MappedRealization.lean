/- GID: D5/S3/Geometry/Gluing/MappedRealization
   generality: G
   mirror-B: none(waiver:consumed-by-weak-category-one-reduction)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An embedding of simplicial vertices gives a realization homeomorphism onto the image. -/

import D5.S3.Geometry.FiniteSimplicialJoin
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Analysis.Convex.Hull

noncomputable section

open Set
open D5.S3.Geometry.FiniteConeCollapse (realization)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)

namespace D5.S3.Geometry.MappedRealization

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Affine coordinates realize the image of a finite complex exactly. -/
theorem linearMap_image_realization (K : PreAbstractSimplicialComplex X) (f : X → Y) :
    FunOnFinite.linearMap ℝ ℝ f '' realization K = realization (K.map f) := by
  let L := FunOnFinite.linearMap ℝ ℝ f
  have faceImage (s : Finset X) :
      L '' convexHull ℝ ((fun x : X => Pi.single x (1 : ℝ)) '' (s : Set X)) =
        convexHull ℝ ((fun y : Y => Pi.single y (1 : ℝ)) '' ((s.image f : Finset Y) : Set Y)) := by
    rw [L.image_convexHull, Set.image_image, Finset.coe_image, Set.image_image]
    congr 1
    apply congrArg (fun g : X → (Y → ℝ) => g '' (s : Set X))
    funext x
    exact FunOnFinite.linearMap_piSingle ℝ ℝ f x 1
  apply Set.Subset.antisymm
  · rintro _ ⟨p, ⟨s, hs, hp⟩, rfl⟩
    refine ⟨s.image f, ⟨s, hs, rfl⟩, ?_⟩
    rw [← faceImage s]
    exact ⟨p, hp, rfl⟩
  · rintro q ⟨_, ⟨s, hs, rfl⟩, hq⟩
    rw [← faceImage s] at hq
    obtain ⟨p, hp, he⟩ := hq
    exact ⟨p, ⟨s, hs, hp⟩, he⟩

private theorem linearMap_apply_image (e : X ↪ Y) (p : X → ℝ) (x : X) :
    FunOnFinite.linearMap ℝ ℝ e p (e x) = p x := by
  rw [FunOnFinite.linearMap_apply_apply]
  have h : Finset.univ.filter (fun a : X => e a = e x) = {x} := by
    ext a
    simp [e.injective.eq_iff]
  rw [h, Finset.sum_singleton]

/-- Relabelling a finite complex by an embedding preserves its realization,
with the original coordinates recovered by restriction along the embedding. -/
def homeomorphMap (K : PreAbstractSimplicialComplex X) (e : X ↪ Y) :
    Space K ≃ₜ Space (K.map e) := by
  let L := FunOnFinite.linearMap ℝ ℝ e
  let forward : Space K → Space (K.map e) := fun p =>
    ⟨L p.val, (linearMap_image_realization K e) ▸ Set.mem_image_of_mem L p.property⟩
  have left (p : X → ℝ) : (fun x => L p (e x)) = p := funext (linearMap_apply_image e p)
  have surj (q : Space (K.map e)) : ∃ p : Space K, forward p = q := by
    have hq : q.val ∈ L '' realization K := (linearMap_image_realization K e).symm ▸ q.property
    obtain ⟨p, hp, he⟩ := hq
    exact ⟨⟨p, hp⟩, Subtype.ext he⟩
  let backward : Space (K.map e) → Space K := fun q =>
    ⟨fun x => q.val (e x), by
      obtain ⟨p, hp⟩ := surj q
      have hq : L p.val = q.val := congrArg Subtype.val hp
      rw [← hq, left]
      exact p.property⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := fun p => Subtype.ext (left p.val)
      right_inv := fun q => by
        obtain ⟨p, rfl⟩ := surj q
        exact congrArg forward (Subtype.ext (left p.val))
      continuous_toFun := ((FunOnFinite.continuous_linearMap ℝ ℝ e).comp
        continuous_subtype_val).subtype_mk _
      continuous_invFun := by
        have hc : Continuous (fun q : Space (K.map e) => fun x : X => q.val (e x)) :=
          continuous_pi fun x => (continuous_apply (e x)).comp continuous_subtype_val
        exact hc.subtype_mk _ }

end D5.S3.Geometry.MappedRealization
