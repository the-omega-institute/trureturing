/- GID: D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/PartitionRelabeling
   mirror-E: none(waiver:exact-configuration-bijection)
   anchors: []
   utility: none
   digest: Graph relabeling transports actual weighted independent configurations exactly. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

variable {α β R : Type*} [DecidableEq α] [DecidableEq β]
variable (G : SimpleGraph α) (H : SimpleGraph β)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- The image of an actual independent configuration is independent exactly
when the original is, under an adjacency-preserving and reflecting relabeling. -/
theorem independent_image_iff (e : α ≃ β)
    (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v) (S : Finset α) :
    H.IsIndepSet (S.image e : Set β) ↔ G.IsIndepSet (S : Set α) := by
  constructor
  · intro h u hu v hv huv
    intro hadj
    exact h (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      (fun hEq => huv (e.injective hEq)) ((he u v).mpr hadj)
  · intro h x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    intro hadj
    exact h hu hv (fun hEq => hxy (congrArg e hEq)) ((he u v).mp hadj)

private theorem image_inverse (e : α ≃ β) (U : Finset β) :
    (U.image e.symm).image e = U := by
  simp [Finset.image_image]

/-- Relabeling bijects the complete independent-configuration families.
This is an equality of finite sets, not an assumed equality of their counts. -/
theorem configurations_relabel (e : α ≃ β)
    (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v) (V : Finset α) :
    configurations H (V.image e) = (configurations G V).image (Finset.image e) := by
  ext U
  constructor
  · intro hU
    have h := Finset.mem_filter.mp hU
    have hsub : U ⊆ V.image e := Finset.mem_powerset.mp h.1
    have hpre : U.image e.symm ⊆ V := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp (hsub hx) with ⟨v, hv, rfl⟩
      simpa using hv
    have hind : G.IsIndepSet (U.image e.symm : Set α) := by
      apply (independent_image_iff G H e he _).mp
      rw [image_inverse]
      exact h.2
    exact Finset.mem_image.mpr ⟨U.image e.symm,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hpre, hind⟩, image_inverse e U⟩
  · intro hU
    rcases Finset.mem_image.mp hU with ⟨S, hS, rfl⟩
    have h := Finset.mem_filter.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, (independent_image_iff G H e he S).mpr h.2⟩
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_powerset.mp h.1) hx, rfl⟩

/-- Every weight is transported along the vertex bijection. In particular,
constant activities give the same polynomial and the same complex values. -/
theorem partition_relabel [CommSemiring R] (e : α ≃ β)
    (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v)
    (V : Finset α) (w : β → R) :
    partition H (V.image e) w = partition G V (fun v => w (e v)) := by
  unfold partition
  rw [configurations_relabel G H e he V]
  calc
    _ = ∑ S ∈ configurations G V, ∏ u ∈ S.image e, w u := by
      apply Finset.sum_image
      intro S _ T _ h
      have h' := congrArg (Finset.image e.symm) h
      simpa [Finset.image_image] using h'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      exact Finset.prod_image (fun x _ y _ h => e.injective h)

/-- Erasing a marked vertex commutes with an exact vertex relabeling. -/
theorem image_erase_equiv (e : α ≃ β) (V : Finset α) (v : α) :
    (V.erase v).image e = (V.image e).erase (e v) := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact Finset.mem_erase.mpr
      ⟨fun h => (Finset.mem_erase.mp hx).1 (e.injective h),
        Finset.mem_image.mpr ⟨x, Finset.mem_of_mem_erase hx, rfl⟩⟩
  · intro hy
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hy
    rcases Finset.mem_image.mp hm with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x,
      Finset.mem_erase.mpr ⟨fun h => hne (congrArg e h), hx⟩, rfl⟩

#print axioms independent_image_iff
#print axioms configurations_relabel
#print axioms partition_relabel
#print axioms image_erase_equiv

end D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
