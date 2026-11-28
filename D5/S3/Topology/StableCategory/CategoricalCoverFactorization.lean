/- GID: D5/S3/Topology/StableCategory/CategoricalCoverFactorization
   generality: G
   mirror-B: none(waiver:cover-factorization-support)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Categorical lower-cover bounds multiply through local factorizations. -/

import Batteries.Tactic.OpenPrivate
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.Topology.SubdivisionCategoricalCover

/-! If each lower region of a finite-space cover factors through a poset
with at most (b) categorical lower sets, the ambient space admits
a categorical lower cover with at most (b) times as many sets. -/

set_option autoImplicit false

namespace D5.S3.Topology.StableCategory.CategoricalCoverFactorization

open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open Relation (EqvGen)

open private map_fence from D5.S3.Topology.SubdivisionCategoricalCover

/-- Pull back covers through local factorizations of the lower-region inclusions
and combine the resulting categorical sets into an ambient lower cover. -/
theorem hasCategoricalCover_of_factorizations {P : Type*} [PartialOrder P] {a b : ℕ}
    (regions : Fin a → Set P) (lower : ∀ i, IsLowerSet (regions i))
    (covers : ∀ x : P, ∃ i, x ∈ regions i)
    {Q : Fin a → Type*} [orders : ∀ i, PartialOrder (Q i)]
    (insert : ∀ i, regions i →o Q i) (project : ∀ i, Q i →o P)
    (hfactor : ∀ i (x : regions i), project i (insert i x) = x.val)
    (hcovers : ∀ i, HasCategoricalCover (Q i) b) : HasCategoricalCover P (a * b) := by
  classical
  let regionCover (i : Fin a) := Classical.choose (hcovers i)
  have hregionCover (i : Fin a) := Classical.choose_spec (hcovers i)
  let piece (ij : Fin a × Fin b) : Set P :=
    {x | ∃ hx : x ∈ regions ij.1, insert ij.1 ⟨x, hx⟩ ∈ regionCover ij.1 ij.2}
  let enumerate : Fin a × Fin b ≃ Fin (a * b) := finProdFinEquiv
  refine ⟨piece ∘ enumerate.symm, ?_, ?_⟩
  · intro e
    let i := (enumerate.symm e).1
    let j := (enumerate.symm e).2
    change IsLowerSet (piece (i, j)) ∧ Categorical (piece (i, j))
    have component := (hregionCover i).1 j
    refine ⟨?_, ?_⟩
    · intro y x hxy hy
      obtain ⟨hyRegion, hyCover⟩ := hy
      have hxRegion := lower i hxy hyRegion
      exact ⟨hxRegion, component.1 ((insert i).monotone (show
        (⟨x, hxRegion⟩ : regions i) ≤ ⟨y, hyRegion⟩ from hxy)) hyCover⟩
    · obtain ⟨c, hc⟩ := component.2
      let toRegion : piece (i, j) →o regions i :=
        ⟨fun x => ⟨x.val, x.property.choose⟩, fun _ _ hxy => hxy⟩
      let into : piece (i, j) →o regionCover i j :=
        ⟨fun x => ⟨insert i (toRegion x), x.property.choose_spec⟩,
          fun _ _ hxy => (insert i).monotone (toRegion.monotone hxy)⟩
      let lift (f : regionCover i j →o Q i) : piece (i, j) →o P :=
        (project i).comp (f.comp into)
      have first : lift (OrderEmbedding.subtype (regionCover i j)).toOrderHom =
          (OrderEmbedding.subtype (piece (i, j))).toOrderHom := by
        ext x
        exact hfactor i (toRegion x)
      have last : lift (OrderHom.const (regionCover i j) c) =
          OrderHom.const (piece (i, j)) (project i c) := rfl
      have step (f g : regionCover i j →o Q i) (hfg : f ≤ g) : lift f ≤ lift g :=
        fun x => (project i).monotone ((OrderHom.le_def.mp hfg) (into x))
      have lifted : EqvGen (· ≤ ·)
          (lift (OrderEmbedding.subtype (regionCover i j)).toOrderHom)
          (lift (OrderHom.const (regionCover i j) c)) :=
        map_fence lift (fun f g hfg => .rel _ _ (step f g hfg)) hc
      rw [first, last] at lifted
      exact ⟨project i c, lifted⟩
  · intro x
    obtain ⟨i, hi⟩ := covers x
    obtain ⟨j, hj⟩ := (hregionCover i).2 (insert i ⟨x, hi⟩)
    refine ⟨enumerate (i, j), ?_⟩
    change x ∈ piece (enumerate.symm (enumerate (i, j)))
    rw [enumerate.symm_apply_apply]
    exact ⟨hi, hj⟩

end D5.S3.Topology.StableCategory.CategoricalCoverFactorization
