/- GID: D5/S3/Topology/Resolution/StoneanFiniteClosedRefinement
   generality: G
   mirror-B: D5/B/S3/Topology/Resolution/StoneanFiniteClosedRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed restrictions of regular open maps yield Stonean finite closed refinements. -/

import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.ShrinkingLemma
import D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

open Set Filter Topology

open D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

namespace D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement

universe u v

/-- A continuous open closed map from a regular space to an extremally
 disconnected space stays open on the closure of any open set, into the whole
 codomain. No compactness, Hausdorffness or surjectivity is assumed. -/
theorem isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected
    {T : Type u} {B : Type v} [TopologicalSpace T] [TopologicalSpace B]
    [RegularSpace T] [ExtremallyDisconnected B] {p : T → B}
    (hp : Continuous p) (hpo : IsOpenMap p) (hpc : IsClosedMap p)
    (W : Set T) (hW : IsOpen W) :
    IsOpenMap (p ∘ (Subtype.val : closure W → T)) := by
  intro V hV
  obtain ⟨O, hO, hVO⟩ :=
    (Topology.IsInducing.subtypeVal (t := closure W)).isOpen_iff.mp hV
  have himage :
      (p ∘ (Subtype.val : closure W → T)) '' V = p '' (O ∩ closure W) := by
    rw [← hVO]
    ext b
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.val, ⟨ht, t.property⟩, rfl⟩
    · rintro ⟨t, ⟨htO, htW⟩, rfl⟩
      exact ⟨⟨t, htW⟩, htO, rfl⟩
  rw [himage]
  apply isOpen_iff_mem_nhds.mpr
  rintro b ⟨t, ⟨htO, htW⟩, rfl⟩
  obtain ⟨N, ⟨htN, hN⟩, hNO⟩ :=
    (hasBasis_opens_closure t).mem_iff.mp (hO.mem_nhds htO)
  have htNW : t ∈ closure (N ∩ W) := by
    apply mem_closure_iff.mpr
    intro R hR htR
    obtain ⟨z, hzRN, hzW⟩ :=
      (mem_closure_iff.mp htW) (R ∩ N) (hR.inter hN) ⟨htR, htN⟩
    exact ⟨z, hzRN.1, hzRN.2, hzW⟩
  have htImage : p t ∈ closure (p '' (N ∩ W)) :=
    image_closure_subset_closure_image hp ⟨t, htNW, rfl⟩
  have hOpen : IsOpen (closure (p '' (N ∩ W))) :=
    ExtremallyDisconnected.open_closure _ (hpo _ (hN.inter hW))
  have hSub : closure (p '' (N ∩ W)) ⊆ p '' (O ∩ closure W) := by
    rw [hpc.closure_image_eq_of_continuous hp (N ∩ W)]
    apply image_mono
    intro z hz
    have hzN : z ∈ closure N := closure_mono inter_subset_left hz
    have hzW : z ∈ closure W := closure_mono inter_subset_right hz
    exact ⟨hNO hzN, hzW⟩
  exact mem_of_superset (hOpen.mem_nhds htImage) hSub


/-- A finite open cover of a regular normal space has a closed subordinate
 refinement whose restrictions of a continuous open closed map are open into
 the whole extremally disconnected codomain. Empty covers and pieces are allowed. -/
theorem hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected
    {T : Type u} {B : Type v} [TopologicalSpace T] [TopologicalSpace B]
    [RegularSpace T] [NormalSpace T] [ExtremallyDisconnected B] {p : T → B}
    (hp : Continuous p) (hpo : IsOpenMap p) (hpc : IsClosedMap p)
    {n : ℕ} (U : Fin n → Set T) (hU : ∀ i, IsOpen (U i))
    (hcover : iUnion U = univ) :
    HasFiniteClosedRefinement p U := by
  classical
  obtain ⟨W, hWcover, hW, hsub⟩ :=
    exists_iUnion_eq_closure_subset hU (fun _ => Set.toFinite _) hcover
  refine ⟨n, (fun i => closure (W i)), id, (fun _ => isClosed_closure), ?_, hsub, ?_⟩
  · intro t
    have ht : t ∈ iUnion W := by rw [hWcover]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨i, subset_closure hi⟩
  · intro i
    exact isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected hp hpo hpc
      (W i) (hW i)

end D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement
