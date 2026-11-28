/- GID: D5/S3/Topology/StableCategory/GraphThickeningForestCover
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/GraphThickeningForestCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ordinary categorical cover number of a graph thickening equals arboricity. -/

import D5.S3.Combinatorics.Graph.Walks.ForestPacking
import D5.S3.Topology.StableCategory.GraphThickeningArboricity
import D5.S3.Topology.StableCategory.GraphThickeningStableCover

/-!
# Ordinary categorical covers of the graph thickening

A spanning forest gives a categorical lower set of the Finset-based
graph thickening. The contractions peel leaves in the induced forest on
the live original vertices, with every comparison in the fixed poset
`P_G G`. This gives the depth-zero upper bound from Section 1 of
`graph-thickening-review.txt` for the graph family in Question 6.3.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.GraphThickeningForestCover

open GraphThickeningStableCover
  (Edge Vertex P_G apex original endpoint endpoint_pair cap side IsConeFace IsSubdividedFace)
open D5.S3.Topology.ConnectedCategoryGraft (Categorical HasCategoricalCover)
open D5.S3.Topology.GraphCycleCategoricalObstruction (HasForestCover arboricity)
open D5.S3.Topology.StableCategory.GraphThickeningArboricity (labels)
open Relation (EqvGen)
open scoped Classical

variable {V : Type*} (G H : SimpleGraph V)

private def liveEdge (W : Finset V) (e : Edge G) : Prop :=
  (e : Sym2 V) ∈ H.edgeSet ∧ endpoint G e 0 ∈ W ∧ endpoint G e 1 ∈ W

private def allowed (W : Finset V) : Vertex G → Prop
  | none => True
  | some (Sum.inl u) => u ∈ W
  | some (Sum.inr e) => liveEdge G H W e

/-- Restrict to live original vertices, the common apex, and midpoints
whose forest edge has both endpoints live. At the initial live set
`univ` this keeps every radial edge. -/
def forestRegion (W : Finset V) : Set (P_G G) :=
  {x | ∀ z ∈ x.val, allowed G H W z}

theorem forestRegion_lower (W : Finset V) : IsLowerSet (forestRegion G H W) :=
  fun _ _ h hx z hz => hx z (h hz)

private theorem mem_edge_iff {e : Edge G} {u : V} :
    u ∈ (e : Sym2 V) ↔ u = endpoint G e 0 ∨ u = endpoint G e 1 := by
  rw [← endpoint_pair G e]
  exact Sym2.mem_iff

private theorem endpoint_mem_edge (e : Edge G) (i : Fin 2) :
    endpoint G e i ∈ (e : Sym2 V) := by
  apply (mem_edge_iff G).mpr
  by_cases hi : i = 0
  · exact Or.inl (congrArg (endpoint G e) hi)
  · exact Or.inr (congrArg (endpoint G e) (Fin.eq_one_of_ne_zero i hi))

private theorem liveEdge_vertex_mem {W : Finset V} {e : Edge G} {u : V}
    (he : liveEdge G H W e) (hu : u ∈ (e : Sym2 V)) : u ∈ W := by
  rcases (mem_edge_iff G).mp hu with h | h
  · exact h.symm ▸ he.2.1
  · exact h.symm ▸ he.2.2

private theorem original_mem_cap_iff {e : Edge G} {u : V} :
    original G u ∈ cap G e ↔ u ∈ (e : Sym2 V) := by
  rw [mem_edge_iff G]
  simp [cap, original, GraphThickeningStableCover.midpoint]

private theorem erase_apex_subset {s t : Finset (Vertex G)}
    (h : s ⊆ insert (apex G) t) : s.erase (apex G) ⊆ t := by
  intro z hz
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hz
  exact (Finset.mem_insert.mp (h hmem)).resolve_left hne

private theorem subset_insert_apex {s t : Finset (Vertex G)}
    (h : s.erase (apex G) ⊆ t) : s ⊆ insert (apex G) t := by
  intro z hz
  by_cases hza : z = apex G
  · exact Finset.mem_insert.mpr (Or.inl hza)
  · exact Finset.mem_insert.mpr (Or.inr (h (Finset.mem_erase.mpr ⟨hza, hz⟩)))

private theorem coneFace_subset {s t : Finset (Vertex G)} (h : s ⊆ t)
    (ht : IsConeFace G t) : IsConeFace G s := by
  have hErase := Finset.erase_subset_erase (apex G) h
  unfold IsConeFace IsSubdividedFace at ht ⊢
  rcases ht with h0 | ⟨v, hv⟩ | ⟨e, i, he⟩
  · exact Or.inl (Finset.subset_empty.mp (h0 ▸ hErase))
  · exact Or.inr (Or.inl ⟨v, hErase.trans hv⟩)
  · exact Or.inr (Or.inr ⟨e, i, hErase.trans he⟩)

private theorem coneFace_insert_apex {s : Finset (Vertex G)} (h : IsConeFace G s) :
    IsConeFace G (insert (apex G) s) := by
  unfold IsConeFace at h ⊢
  rwa [Finset.erase_insert_eq_erase]

private theorem coneFace_of_subset_cone_side {s : Finset (Vertex G)} {e : Edge G} {i : Fin 2}
    (hs : s ⊆ insert (apex G) (side G e i)) : IsConeFace G s :=
  Or.inr (Or.inr ⟨e, i, erase_apex_subset G hs⟩)

/-- A cone face through an original vertex is radial or contains the
midpoint on one of its sides. The second case provides an actual midpoint
in the face, so a region membership proof supplies its forest edge. -/
private theorem coneFace_containing_original {s : Finset (Vertex G)} {u : V}
    (hs : IsConeFace G s) (hu : original G u ∈ s) :
    s ⊆ insert (apex G) {original G u} ∨
      ∃ (e : Edge G) (i : Fin 2), GraphThickeningStableCover.midpoint G e ∈ s ∧
        u = endpoint G e i := by
  have huErase : original G u ∈ s.erase (apex G) :=
    Finset.mem_erase.mpr ⟨by simp [original, apex], hu⟩
  unfold IsConeFace IsSubdividedFace at hs
  rcases hs with h0 | ⟨v, hv⟩ | ⟨e, i, he⟩
  · exact (Finset.notMem_empty _ (h0 ▸ huErase)).elim
  · have huv : u = v := by
      simpa [original] using Finset.mem_singleton.mp (hv huErase)
    subst v
    exact Or.inl (subset_insert_apex G hv)
  · have hui : u = endpoint G e i := by
      simpa [side, original, GraphThickeningStableCover.midpoint] using he huErase
    by_cases hm : GraphThickeningStableCover.midpoint G e ∈ s
    · exact Or.inr ⟨e, i, hm, hui⟩
    · refine Or.inl (subset_insert_apex G ?_)
      intro z hz
      have hz' := he hz
      change z ∈ insert (original G (endpoint G e i)) {GraphThickeningStableCover.midpoint G e} at hz'
      rcases Finset.mem_insert.mp hz' with hz' | hz'
      · exact Finset.mem_singleton.mpr (hz'.trans (congrArg (original G) hui.symm))
      · exact (hm (Finset.mem_singleton.mp hz' ▸ Finset.mem_of_mem_erase hz)).elim

private theorem coneFace_erase_cap_original {e : Edge G} {u : V}
    (hu : u ∈ (e : Sym2 V)) : IsConeFace G ((cap G e).erase (original G u)) := by
  have ofSide (i : Fin 2) (h : (cap G e).erase (original G u) ⊆ side G e i) :
      IsConeFace G ((cap G e).erase (original G u)) :=
    coneFace_of_subset_cone_side G (h.trans (Finset.subset_insert _ _))
  rcases (mem_edge_iff G).mp hu with h | h
  · subst u
    apply ofSide 1
    intro z hz
    obtain ⟨hne, hcap⟩ := Finset.mem_erase.mp hz
    simp only [cap, Finset.mem_insert, Finset.mem_singleton] at hcap
    simp only [side, Finset.mem_insert, Finset.mem_singleton]
    rcases hcap with h | h | h
    · exact (hne h).elim
    · exact Or.inr h
    · exact Or.inl h
  · subst u
    apply ofSide 0
    intro z hz
    obtain ⟨hne, hcap⟩ := Finset.mem_erase.mp hz
    simp only [cap, Finset.mem_insert, Finset.mem_singleton] at hcap
    simp only [side, Finset.mem_insert, Finset.mem_singleton]
    exact hcap.imp_right (fun h => h.resolve_right hne)

private theorem midpoint_unique (x : P_G G) {e f : Edge G}
    (he : GraphThickeningStableCover.midpoint G e ∈ x.val)
    (hf : GraphThickeningStableCover.midpoint G f ∈ x.val) : e = f := by
  rcases x.property.2 with hc | ⟨d, hd⟩
  · have he' : GraphThickeningStableCover.midpoint G e ∈ x.val.erase (apex G) :=
      Finset.mem_erase.mpr ⟨by simp [GraphThickeningStableCover.midpoint, apex], he⟩
    have hf' : GraphThickeningStableCover.midpoint G f ∈ x.val.erase (apex G) :=
      Finset.mem_erase.mpr ⟨by simp [GraphThickeningStableCover.midpoint, apex], hf⟩
    unfold IsConeFace IsSubdividedFace at hc
    rcases hc with h0 | ⟨v, hv⟩ | ⟨d, i, hi⟩
    · exact (Finset.notMem_empty _ (h0 ▸ he')).elim
    · have h := hv he'
      simp [GraphThickeningStableCover.midpoint, original] at h
    · have hed : e = d := by simpa [side, GraphThickeningStableCover.midpoint, original] using hi he'
      have hfd : f = d := by simpa [side, GraphThickeningStableCover.midpoint, original] using hi hf'
      exact hed.trans hfd.symm
  · rw [hd] at he hf
    have hed : e = d := by simpa [cap, GraphThickeningStableCover.midpoint, original] using he
    have hfd : f = d := by simpa [cap, GraphThickeningStableCover.midpoint, original] using hf
    exact hed.trans hfd.symm

private def replaceVertex (a b : Vertex G) (z : Vertex G) : Vertex G :=
  if z = a then b else z

private abbrev replaceImage (a b : Vertex G) (s : Finset (Vertex G)) : Finset (Vertex G) :=
  s.image (replaceVertex G a b)

private theorem mem_replaceImage {a b z : Vertex G} {s : Finset (Vertex G)}
    (hz : z ∈ replaceImage G a b s) : z = b ∨ (z ∈ s ∧ z ≠ a) := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  by_cases h : v = a
  · exact Or.inl (if_pos h)
  · rw [replaceVertex, if_neg h]
    exact Or.inr ⟨hv, h⟩

private theorem replaceImage_subset_insert (a b : Vertex G) (s : Finset (Vertex G)) :
    replaceImage G a b s ⊆ insert b s :=
  fun _ hz => Finset.mem_insert.mpr ((mem_replaceImage G hz).imp_right And.left)

private theorem notMem_replaceImage_source {a b : Vertex G} {s : Finset (Vertex G)}
    (hab : a ≠ b) : a ∉ replaceImage G a b s := by
  intro ha
  rcases mem_replaceImage G ha with h | ⟨_, h⟩
  · exact hab h
  · exact h rfl

private theorem replaceImage_eq_self {a b : Vertex G} {s : Finset (Vertex G)}
    (ha : a ∉ s) : replaceImage G a b s = s := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
    have hne : v ≠ a := fun h => ha (h ▸ hv)
    rw [replaceVertex, if_neg hne] at hvz
    exact hvz ▸ hv
  · intro z hz
    have hne : z ≠ a := fun h => ha (h ▸ hz)
    exact Finset.mem_image.mpr ⟨z, hz, if_neg hne⟩

private theorem union_replaceImage_of_mem {a b : Vertex G} {s : Finset (Vertex G)}
    (ha : a ∈ s) : s ∪ replaceImage G a b s = insert b s := by
  apply Finset.Subset.antisymm
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.mem_insert_of_mem hz
    · exact replaceImage_subset_insert G a b s hz
  · apply Finset.insert_subset
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, if_pos rfl⟩)
    · exact fun _ hz => Finset.mem_union_left _ hz

private abbrev regionInclusion (A : Set (P_G G)) : A →o P_G G :=
  (OrderEmbedding.subtype A).toOrderHom

/-- A fence in the ambient poset from the inclusion to a map taking
values in the specified smaller region. -/
def FoldsInto (A B : Set (P_G G)) : Prop :=
  ∃ f : A →o B, EqvGen (· ≤ ·) (regionInclusion G A) ((regionInclusion G B).comp f)

private theorem precomposeFence {A B : Set (P_G G)} (f : A →o B)
    {p q : B →o P_G G} (h : EqvGen (· ≤ ·) p q) :
    EqvGen (· ≤ ·) (p.comp f) (q.comp f) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (fun x => OrderHom.le_def.mp h (f x))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem foldsInto_trans {A B C : Set (P_G G)}
    (hAB : FoldsInto G A B) (hBC : FoldsInto G B C) : FoldsInto G A C := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨g.comp f, .trans _ _ _ hf (precomposeFence G f hg)⟩

/-- The image map and the inclusion are both pointwise below the map
with values given by the union of the face and its image. -/
private theorem foldsInto_of_replace (A B : Set (P_G G)) (a b : Vertex G)
    (hfaces : ∀ x : A, a ∈ x.val.val →
      IsConeFace G (replaceImage G a b x.val.val) ∧
      (IsConeFace G (insert b x.val.val) ∨ ∃ e : Edge G, insert b x.val.val = cap G e))
    (hB : ∀ (x : A) (y : P_G G), y.val = replaceImage G a b x.val.val → y ∈ B) :
    FoldsInto G A B := by
  let image (x : A) : P_G G := ⟨replaceImage G a b x.val.val,
    x.val.property.1.image _, by
      by_cases ha : a ∈ x.val.val
      · exact Or.inl (hfaces x ha).1
      · rw [replaceImage_eq_self G ha]
        exact x.val.property.2⟩
  let f : A →o B :=
    ⟨fun x => ⟨image x, hB x (image x) rfl⟩, by
      intro x y hxy
      change replaceImage G a b x.val.val ⊆ replaceImage G a b y.val.val
      exact Finset.image_subset_image (show x.val.val ⊆ y.val.val from hxy)⟩
  let join : A →o P_G G :=
    ⟨fun x => ⟨x.val.val ∪ (image x).val, by
        obtain ⟨z, hz⟩ := x.val.property.1
        exact ⟨z, Finset.mem_union_left _ hz⟩, by
        change IsConeFace G (x.val.val ∪ replaceImage G a b x.val.val) ∨
          ∃ e : Edge G, x.val.val ∪ replaceImage G a b x.val.val = cap G e
        by_cases ha : a ∈ x.val.val
        · rw [union_replaceImage_of_mem G ha]
          exact (hfaces x ha).2
        · simpa only [replaceImage_eq_self G ha, Finset.union_self] using x.val.property.2⟩, by
      intro x y hxy z hz
      change z ∈ x.val.val ∪ replaceImage G a b x.val.val at hz
      change z ∈ y.val.val ∪ replaceImage G a b y.val.val
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ ((show x.val.val ⊆ y.val.val from hxy) hz)
      · exact Finset.mem_union_right _
          (Finset.image_subset_image (show x.val.val ⊆ y.val.val from hxy) hz)⟩
  have hincl : regionInclusion G A ≤ join :=
    fun x _ hz => Finset.mem_union_left (image x).val hz
  have himage : (regionInclusion G B).comp f ≤ join :=
    fun x _ hz => Finset.mem_union_right x.val.val hz
  exact ⟨f, .trans _ _ _ (.rel _ _ hincl) (.symm _ _ (.rel _ _ himage))⟩

private theorem mem_region_of_image {W : Finset V} {a b : Vertex G}
    {x y : P_G G} (hx : x ∈ forestRegion G H W) (hb : allowed G H W b)
    (hy : y.val = replaceImage G a b x.val) : y ∈ forestRegion G H W := by
  intro z hz
  rw [hy] at hz
  rcases mem_replaceImage G hz with rfl | ⟨hz, _⟩
  · exact hb
  · exact hx z hz

private theorem mem_region_erase {W : Finset V} {u : V} {x : P_G G}
    (hx : x ∈ forestRegion G H W) (hu : original G u ∉ x.val)
    (hmid : ∀ e : Edge G, u ∈ (e : Sym2 V) → GraphThickeningStableCover.midpoint G e ∉ x.val) :
    x ∈ forestRegion G H (W.erase u) := by
  intro z hz
  cases z with
  | none => exact trivial
  | some z =>
    cases z with
    | inl v =>
      have hv : v ∈ W := hx _ hz
      exact Finset.mem_erase.mpr ⟨fun h => hu (h ▸ hz), hv⟩
    | inr e =>
      have he : liveEdge G H W e := hx _ hz
      have hne (i : Fin 2) : endpoint G e i ≠ u := by
        intro hi
        exact hmid e (hi ▸ endpoint_mem_edge G e i) hz
      exact ⟨he.1, Finset.mem_erase.mpr ⟨hne 0, he.2.1⟩,
        Finset.mem_erase.mpr ⟨hne 1, he.2.2⟩⟩

private theorem live_incident_edge_eq {W : Finset V} (u : (W : Set V))
    (hleaf : ((H.induce (W : Set V)).neighborSet u).Subsingleton)
    {e f : Edge G} (he : liveEdge G H W e) (hf : liveEdge G H W f)
    (heu : u.val ∈ (e : Sym2 V)) (hfu : u.val ∈ (f : Sym2 V)) : e = f := by
  obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp heu
  obtain ⟨w, hfw⟩ := Sym2.mem_iff_exists.mp hfu
  have hv : v ∈ W := liveEdge_vertex_mem G H he (hev.symm ▸ Sym2.mem_mk_right u.val v)
  have hw : w ∈ W := liveEdge_vertex_mem G H hf (hfw.symm ▸ Sym2.mem_mk_right u.val w)
  have huv : H.Adj u.val v := H.mem_edgeSet.mp (hev ▸ he.1)
  have huw : H.Adj u.val w := H.mem_edgeSet.mp (hfw ▸ hf.1)
  have h : (⟨v, hv⟩ : (W : Set V)) = ⟨w, hw⟩ := hleaf
    (show (⟨v, hv⟩ : (W : Set V)) ∈ (H.induce (W : Set V)).neighborSet u from huv)
    (show (⟨w, hw⟩ : (W : Set V)) ∈ (H.induce (W : Set V)).neighborSet u from huw)
  have hvw : v = w := congrArg Subtype.val h
  apply Subtype.ext
  change (e : Sym2 V) = (f : Sym2 V)
  rw [hev, hfw, hvw]

private theorem replace_original_by_midpoint_faces {W : Finset V} {u : V} {e : Edge G}
    (hue : u ∈ (e : Sym2 V))
    (hunique : ∀ f : Edge G, liveEdge G H W f → u ∈ (f : Sym2 V) → f = e)
    (x : forestRegion G H W) (hu : original G u ∈ x.val.val) :
    IsConeFace G (replaceImage G (original G u) (GraphThickeningStableCover.midpoint G e) x.val.val) ∧
      (IsConeFace G (insert (GraphThickeningStableCover.midpoint G e) x.val.val) ∨
        ∃ f : Edge G, insert (GraphThickeningStableCover.midpoint G e) x.val.val = cap G f) := by
  have ofCone (h : IsConeFace G (insert (GraphThickeningStableCover.midpoint G e) x.val.val)) :
      IsConeFace G (replaceImage G (original G u) (GraphThickeningStableCover.midpoint G e) x.val.val) ∧
        (IsConeFace G (insert (GraphThickeningStableCover.midpoint G e) x.val.val) ∨
          ∃ f : Edge G, insert (GraphThickeningStableCover.midpoint G e) x.val.val = cap G f) :=
    ⟨coneFace_subset G (replaceImage_subset_insert G _ _ _) h, Or.inl h⟩
  rcases x.val.property.2 with hc | ⟨f, hf⟩
  · apply ofCone
    rcases coneFace_containing_original G hc hu with hradial | ⟨f, i, hmid, hui⟩
    · have radial (i : Fin 2) (hi : u = endpoint G e i) :
          IsConeFace G (insert (GraphThickeningStableCover.midpoint G e) x.val.val) := by
        apply coneFace_of_subset_cone_side G (e := e) (i := i)
        apply Finset.insert_subset
        · simp [side]
        · apply hradial.trans
          exact Finset.insert_subset_insert _ (by simp [side, hi])
      rcases (mem_edge_iff G).mp hue with h | h
      · exact radial 0 h
      · exact radial 1 h
    · have huf : u ∈ (f : Sym2 V) := hui.symm ▸ endpoint_mem_edge G f i
      have hfe := hunique f (x.property _ hmid) huf
      subst f
      simpa only [Finset.insert_eq_of_mem hmid] using hc
  · have hmid : GraphThickeningStableCover.midpoint G f ∈ x.val.val := by rw [hf]; simp [cap]
    have huf : u ∈ (f : Sym2 V) := (original_mem_cap_iff G).mp (hf ▸ hu)
    have hfe := hunique f (x.property _ hmid) huf
    subst f
    refine ⟨coneFace_subset G ?_ (coneFace_erase_cap_original G hue), Or.inr ⟨e, ?_⟩⟩
    · intro z hz
      apply Finset.mem_erase.mpr
      rcases mem_replaceImage G hz with rfl | ⟨hz, hne⟩
      · exact ⟨by simp [GraphThickeningStableCover.midpoint, original], by simp [cap]⟩
      · exact ⟨hne, hf ▸ hz⟩
    · rw [Finset.insert_eq_of_mem hmid, hf]

/-- On the live forest, peel one vertex of degree at most one. If it
has an incident edge, the first fence replaces the vertex by the
private midpoint and the second replaces that midpoint by the apex. -/
theorem leaf_transition (W : Finset V) {u : V} (hu : u ∈ W)
    (hleaf : ((H.induce (W : Set V)).neighborSet ⟨u, hu⟩).Subsingleton) :
    FoldsInto G (forestRegion G H W) (forestRegion G H (W.erase u)) := by
  let A := forestRegion G H W
  let B := forestRegion G H (W.erase u)
  by_cases hex : ∃ e : Edge G, liveEdge G H W e ∧ u ∈ (e : Sym2 V)
  · obtain ⟨e, he, hue⟩ := hex
    have hunique (f : Edge G) (hf : liveEdge G H W f) (huf : u ∈ (f : Sym2 V)) :
        f = e :=
      live_incident_edge_eq G H ⟨u, hu⟩ hleaf hf he huf hue
    let M : Set (P_G G) := {x | x ∈ A ∧ original G u ∉ x.val}
    have h₁ : FoldsInto G A M := by
      apply foldsInto_of_replace G A M (original G u) (GraphThickeningStableCover.midpoint G e)
        (replace_original_by_midpoint_faces G H hue hunique)
      intro x y hy
      have hmid : allowed G H W (GraphThickeningStableCover.midpoint G e) := he
      refine ⟨mem_region_of_image G H x.property hmid hy, ?_⟩
      rw [hy]
      exact notMem_replaceImage_source G (by simp [original, GraphThickeningStableCover.midpoint])
    have h₂ : FoldsInto G M B := by
      apply foldsInto_of_replace G M B (GraphThickeningStableCover.midpoint G e) (apex G)
      · intro x hmid
        have hc : IsConeFace G x.val.val := by
          rcases x.val.property.2 with hc | ⟨f, hf⟩
          · exact hc
          · have hef : e = f := by
              rw [hf] at hmid
              simpa [cap, original, GraphThickeningStableCover.midpoint] using hmid
            subst f
            exact (x.property.2 (hf.symm ▸ (original_mem_cap_iff G).mpr hue)).elim
        have hj := coneFace_insert_apex G hc
        exact ⟨coneFace_subset G (replaceImage_subset_insert G _ _ _) hj, Or.inl hj⟩
      · intro x y hy
        have hyA := mem_region_of_image G H x.property.1 (show allowed G H W (apex G) from trivial) hy
        apply mem_region_erase G H hyA
        · intro hu'
          rw [hy] at hu'
          rcases mem_replaceImage G hu' with h | ⟨h, _⟩
          · simpa [original, apex] using h
          · exact x.property.2 h
        · intro f huf hf
          have hfe := hunique f (hyA _ hf) huf
          subst f
          exact notMem_replaceImage_source G
            (by simp [GraphThickeningStableCover.midpoint, apex]) (hy ▸ hf)
    exact foldsInto_trans G h₁ h₂
  · apply foldsInto_of_replace G A B (original G u) (apex G)
    · intro x hu'
      have hc : IsConeFace G x.val.val := by
        rcases x.val.property.2 with hc | ⟨f, hf⟩
        · exact hc
        · have hmid : GraphThickeningStableCover.midpoint G f ∈ x.val.val := by rw [hf]; simp [cap]
          exact (hex ⟨f, x.property _ hmid, (original_mem_cap_iff G).mp (hf ▸ hu')⟩).elim
      have hj := coneFace_insert_apex G hc
      exact ⟨coneFace_subset G (replaceImage_subset_insert G _ _ _) hj, Or.inl hj⟩
    · intro x y hy
      have hyA := mem_region_of_image G H x.property (show allowed G H W (apex G) from trivial) hy
      apply mem_region_erase G H hyA
      · rw [hy]
        exact notMem_replaceImage_source G (by simp [original, apex])
      · exact fun f huf hf => hex ⟨f, hyA _ hf, huf⟩

private def apexFace : P_G G :=
  ⟨{apex G}, Finset.singleton_nonempty _, Or.inl (Or.inl (by simp))⟩

private theorem empty_region_eq_apex (x : forestRegion G H ∅) : x.val = apexFace G := by
  apply Subtype.ext
  have hsub : x.val.val ⊆ {apex G} := by
    intro z hz
    have h := x.property z hz
    cases z with
    | none => simp [apex]
    | some z =>
      cases z with
      | inl u => exact (Finset.notMem_empty u h).elim
      | inr e => exact (Finset.notMem_empty _ (show liveEdge G H ∅ e from h).2.1).elim
  change x.val.val = {apex G}
  refine Finset.Subset.antisymm hsub ?_
  obtain ⟨z, hz⟩ := x.val.property.1
  have heq := Finset.mem_singleton.mp (hsub hz)
  intro a ha
  rw [Finset.mem_singleton.mp ha, ← heq]
  exact hz

/-- The live region of a finite forest contracts in the fixed ambient
poset to the common singleton apex. -/
theorem forestRegion_contracts [Finite V] (hH : H.IsAcyclic) (W : Finset V) :
    EqvGen (· ≤ ·) (regionInclusion G (forestRegion G H W))
      (OrderHom.const (forestRegion G H W) (apexFace G)) := by
  refine Finset.strongInductionOn W ?_
  intro W ih
  by_cases hW : W.Nonempty
  · obtain ⟨v, hv⟩ := hW
    letI : Nonempty (W : Set V) := ⟨⟨v, hv⟩⟩
    obtain ⟨u, hu⟩ := SimpleGraph.ForestPacking.exists_leaf_of_finite_forest
      (hH.induce (W : Set V))
    obtain ⟨r, hr⟩ := leaf_transition G H W u.property hu
    have h := precomposeFence G r (ih (W.erase u.val) (Finset.erase_ssubset u.property))
    exact .trans _ _ _ hr h
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    have h : regionInclusion G (forestRegion G H ∅) =
        OrderHom.const (forestRegion G H ∅) (apexFace G) := by
      apply OrderHom.ext
      funext x
      exact empty_region_eq_apex G H x
    rw [h]
    exact .refl _

theorem forestRegion_categorical [Finite V] (hH : H.IsAcyclic) (W : Finset V) :
    Categorical (forestRegion G H W) :=
  ⟨apexFace G, forestRegion_contracts G H hH W⟩

/-- Even an edgeless thickening contains the common apex. -/
theorem pos_of_hasCategoricalCover {n : ℕ} (h : HasCategoricalCover (P_G G) n) : 0 < n := by
  obtain ⟨_, _, cover⟩ := h
  obtain ⟨i, _⟩ := cover (apexFace G)
  exact (Nat.zero_le i.val).trans_lt i.isLt

private theorem mem_region_univ [Fintype V] (x : P_G G)
    (hmid : ∀ e : Edge G, GraphThickeningStableCover.midpoint G e ∈ x.val → (e : Sym2 V) ∈ H.edgeSet) :
    x ∈ forestRegion G H Finset.univ := by
  intro z hz
  cases z with
  | none => exact trivial
  | some z =>
    cases z with
    | inl u => exact Finset.mem_univ u
    | inr e => exact ⟨hmid e hz, Finset.mem_univ _, Finset.mem_univ _⟩

/-- A positive indexed forest cover of the edges gives an ordinary
categorical cover with the same number of pieces. Positivity lets us
assign a face with no midpoint to a piece, even if the graph is edgeless. -/
theorem hasCategoricalCover_of_hasForestCover [Finite V] {n : ℕ}
    (hn : 0 < n) (h : HasForestCover G n) : HasCategoricalCover (P_G G) n := by
  obtain ⟨F, hF, cover⟩ := h
  letI : Fintype V := Fintype.ofFinite V
  refine ⟨fun i => forestRegion G (F i) Finset.univ, fun i =>
    ⟨forestRegion_lower G (F i) _, forestRegion_categorical G (F i) (hF i).2 _⟩, ?_⟩
  intro x
  by_cases hm : ∃ e : Edge G, GraphThickeningStableCover.midpoint G e ∈ x.val
  · obtain ⟨e, he⟩ := hm
    obtain ⟨i, hi⟩ := cover e.val e.property
    refine ⟨i, mem_region_univ G (F i) x ?_⟩
    intro f hf
    have hfe := midpoint_unique G x hf he
    exact hfe.symm ▸ hi
  · exact ⟨⟨0, hn⟩, mem_region_univ G (F ⟨0, hn⟩) x (fun e he => (hm ⟨e, he⟩).elim)⟩

/-- For a graph with an edge, its thickening has exactly the same feasible
ordinary categorical cover sizes as the original graph has forest cover sizes. -/
theorem hasCategoricalCover_iff_hasForestCover [Finite V] (hEdge : Nonempty (Edge G)) {n : ℕ} :
    HasCategoricalCover (P_G G) n ↔ HasForestCover G n := by
  constructor
  · exact (labels G).hasForestCover_of_hasCategoricalCover
  · intro h
    have hn : 0 < n := by
      obtain ⟨e⟩ := hEdge
      obtain ⟨F, _, hc⟩ := h
      obtain ⟨i, _⟩ := hc e.val e.property
      exact (Nat.zero_le i.val).trans_lt i.isLt
    exact hasCategoricalCover_of_hasForestCover G hn h

/-- The ordinary categorical cover number of the thickening of a finite
graph with an edge equals its arboricity. -/
theorem ordinary_cover_number_eq_arboricity [Finite V] (hEdge : Nonempty (Edge G)) :
    sInf {n | HasCategoricalCover (P_G G) n} = arboricity G := by
  have heq : {n | HasCategoricalCover (P_G G) n} = {n | HasForestCover G n} := by
    ext n
    exact hasCategoricalCover_iff_hasForestCover G hEdge
  exact congrArg sInf heq

end D5.S3.Topology.StableCategory.GraphThickeningForestCover
