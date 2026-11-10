/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryForests
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryForests
   mirror-E: none(waiver:original-projected-path-forest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]
   utility: none
   digest: Literal projected wheel-path rows, redundant supersets, cut intervals and original endpoint markers. -/

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryForestComponents
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalMWheel
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
attribute [local instance] historyForestsPropDecidable
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
open OriginalLabelTwoSum HistoryCorners AllMWheel


open private
  position_lt
  at_position
  at_injective
  interval_symm
  interval_trans
  mem_component
  self_component
  block_supported
  at_leftEnd
  at_rightEnd
  from D5.S3.Geometry.OriginalLabelTwoSum.HistoryForestComponents


section Markers
variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

/-- Surviving ORIGINAL interface markers, not endpoints invented after projection. -/
def markers : Finset (Label m) := rim m hm ∩ (localRows m hm A B).ground

private theorem residual_without_markers :
    (localRows m hm A B).ground \ markers m hm A B =
      (localRows m hm A B).ground \ rim m hm := by
  ext x
  simp only [markers, Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- This data is constructed from actual masks. Its proof fields are OUTPUTS;
there is no constructor argument of this type in classifyMarkers. -/
inductive MarkerCase : Type
  | absent (h : ¬ Disjoint A (rim m hm))
  | absorbed (h : Disjoint A (rim m hm))
      (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty)
  | noMarker (h : Disjoint A (rim m hm))
      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))
      (hR : markers m hm A B = ∅)
  | oneMarker (h : Disjoint A (rim m hm))
      (a : Fin m) (ha : a ∈ live m hm A B)
      (hF : «at» m hm a ∉ forced (localRows m hm A B))
      (hR : markers m hm A B = {«at» m hm a})
  | separated (h : Disjoint A (rim m hm))
      (hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B))
      (hR : markers m hm A B = rim m hm)
      (apart : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)))
  | intact (hA : A = ∅) (hB : B = ∅)
      (hF : forced (localRows m hm A B) = ∅)
      (full : component m hm A B (leftEnd m hm) = Finset.univ)
      (sole : components m hm A B = {Finset.univ})
      (labels : block m hm A B (leftEnd m hm) = ground m)
      (root : (localRows m hm A B).root = pathRoot m hm)

/-- TOTAL exhaustive classification for every width and every local original mask.
A surviving marker is forced precisely by a singleton row, never by support loss. -/
def classifyMarkers (hA : A ⊆ ground m) (hB : B ⊆ ground m) :
    MarkerCase m hm A B := by
  classical
  by_cases h : Disjoint A (rim m hm)
  · by_cases hF : Disjoint (forced (localRows m hm A B)) (markers m hm A B)
    · by_cases hf : firstLabel m hm ∈ (localRows m hm A B).ground
      · by_cases hs : secondLabel m hm ∈ (localRows m hm A B).ground
        · have hR : markers m hm A B = rim m hm := by
            ext x
            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · exact fun hh => hh.1
            · rintro (rfl | rfl) <;> simp_all
          by_cases hc : Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))
          · obtain ⟨hAe, hBe, hFe, full, sole, labels, root⟩ :=
              endpoints_connected_untouched m hm A B hA hB hc
            exact .intact hAe hBe hFe full sole labels root
          · exact .separated h hF hR hc
        · have hR : markers m hm A B = {«at» m hm (rightEnd m hm)} := by
            rw [at_rightEnd]
            ext x
            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hx⟩; rfl; exact (hs hx).elim
            · rintro rfl; exact ⟨Or.inl rfl, hf⟩
          exact .oneMarker h (rightEnd m hm) (by simp [live, at_rightEnd, hf])
            (fun hff => Finset.disjoint_left.mp hF hff (by simp [hR])) hR
      · by_cases hs : secondLabel m hm ∈ (localRows m hm A B).ground
        · have hR : markers m hm A B = {«at» m hm (leftEnd m hm)} := by
            rw [at_leftEnd]
            ext x
            simp only [markers, rim, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hx⟩; exact (hf hx).elim; rfl
            · rintro rfl; exact ⟨Or.inr rfl, hs⟩
          exact .oneMarker h (leftEnd m hm) (by simp [live, at_leftEnd, hs])
            (fun hff => Finset.disjoint_left.mp hF hff (by simp [hR])) hR
        · apply MarkerCase.noMarker h hF
          ext x
          simp only [markers, rim, Finset.mem_inter, Finset.mem_insert,
            Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨rfl | rfl, hx⟩
          · exact hf hx
          · exact hs hx
    · have hFR : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty := by
        obtain ⟨x, hxF, hxR⟩ := Finset.not_disjoint_iff.mp hF
        exact ⟨x, Finset.mem_inter.mpr ⟨hxF, hxR⟩⟩
      exact .absorbed h hFR
  · exact .absent h

/-- The two surviving separated markers really occupy disjoint components. -/
theorem separated_components
    (hL : leftEnd m hm ∈ live m hm A B) (hR : rightEnd m hm ∈ live m hm A B)
    (h : ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm))) :
    Disjoint (component m hm A B (leftEnd m hm))
      (component m hm A B (rightEnd m hm)) := by
  rcases component_partition m hm A B _ _ hL hR with he | hd
  · have hx := self_component m hm A B (rightEnd m hm) hR
    rw [← he] at hx
    exact (h ((Finset.mem_filter.mp hx).2)).elim
  · exact hd

/-- Literal last-wheel parent factor on an arbitrary physical ambient type.
The old X,D,L coordinates need not fit inside the wheel's finite label type. -/
def decorated {V : Type*} [Fintype V] [DecidableEq V] (f : Label m ↪ V)
    (X : Finset V) (D L : Family V) : Family V :=
  (rawJoin (delta X) (renameFamily f (localRows m hm A B).root) ⊔
    rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔
    if Disjoint A (rim m hm) then
      rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f)) else ⊥

/-- A singleton at an actual surviving interface marker absorbs the D fibre.
No old label or HistoryCorners.residual local ghost is removed by this family equality. -/
theorem forced_marker_absorbs {V : Type*} [Fintype V] [DecidableEq V]
    (f : Label m ↪ V) (X : Finset V) (D : Family V) (hD : Supported X D)
    (hF : (forced (localRows m hm A B) ∩ markers m hm A B).Nonempty) :
    rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f)) ≤
      rawJoin (delta X) (renameFamily f (localRows m hm A B).root) := by
  obtain ⟨z, hz⟩ := hF
  obtain ⟨hzF, hzR⟩ := Finset.mem_inter.mp hz
  obtain ⟨c, hc⟩ := (mem_forced _ z).mp hzF
  have hzrim : z ∈ rim m hm := (Finset.mem_inter.mp hzR).1
  rintro s ⟨u, hu, v, hv, rfl⟩
  obtain ⟨t, ht, rfl⟩ := Finset.subset_image_iff.mp hv
  refine ⟨u, hD u hu, t.image f, ⟨t, ⟨c, ?_⟩, rfl⟩, rfl⟩
  intro x hx
  obtain ⟨hxU, hxr⟩ := Finset.mem_sdiff.mp (ht hx)
  refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
  intro hxq
  have he : x = z := by simpa [hc] using hxq
  exact hxr (he.symm ▸ hzrim)

/-- The computed case is consumed in the actual ambient factor normal form. -/
def markerNormalForm {V : Type*} [Fintype V] [DecidableEq V] (f : Label m ↪ V)
    (X : Finset V) (D L : Family V) : MarkerCase m hm A B → Family V
  | .absent _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔
      rawJoin L (delta ((localRows m hm A B).ground.image f))
  | .absorbed _ _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔
      rawJoin L (delta ((localRows m hm A B).ground.image f))
  | .noMarker _ _ _ => rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔
      rawJoin D (delta ((localRows m hm A B).ground.image f))
  | .oneMarker _ a _ _ _ =>
      (rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔
        rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔
      rawJoin D (delta (((localRows m hm A B).ground \ {«at» m hm a}).image f))
  | .separated _ _ _ _ =>
      (rawJoin (delta X) (renameFamily f (componentUnion m hm A B)) ⊔
        rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔
      rawJoin D (delta (((localRows m hm A B).ground \ rim m hm).image f))
  | .intact _ _ _ _ _ _ _ =>
      (rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔ rawJoin L (delta ((ground m).image f))) ⊔
      rawJoin D (delta ((tailGround m hm).image f))

/-- Exhaustive actual-mask consumer. Earlier face factors have only their genuine
support and L≤D; no classification, forest, equality, Output or collapse is assumed. -/
theorem decorated_readback {V : Type*} [Fintype V] [DecidableEq V]
    (hA : A ⊆ ground m) (hB : B ⊆ ground m)
    (h0 : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)
    (f : Label m ↪ V) (X : Finset V) (D L : Family V)
    (hD : Supported X D) (hLD : L ≤ D) :
    decorated m hm A B f X D L =
      markerNormalForm m hm A B f X D L (classifyMarkers m hm A B hA hB) := by
  have hE := congrArg (renameFamily f) (component_root m hm A B h0)
  generalize he : classifyMarkers m hm A B hA hB = c
  cases c with
  | absent h => simp only [decorated, markerNormalForm, if_neg h, sup_bot_eq, hE]
  | absorbed h hf =>
      have hle := forced_marker_absorbs m hm A B f X D hD hf
      rw [decorated, if_pos h, sup_eq_left.mpr (hle.trans le_sup_left)]
      simp only [markerNormalForm, hE]
  | noMarker h hf hr =>
      have hg : (localRows m hm A B).ground \ rim m hm = (localRows m hm A B).ground := by
        rw [← residual_without_markers m hm A B, hr, Finset.sdiff_empty]
      have hle : rawJoin L (delta ((localRows m hm A B).ground.image f)) ≤
          rawJoin D (delta ((localRows m hm A B).ground.image f)) := by
        rintro s ⟨u, hu, v, hv, rfl⟩
        exact ⟨u, hLD hu, v, hv, rfl⟩
      simp only [decorated, markerNormalForm, if_pos h, hg, hE]
      rw [sup_assoc, sup_eq_right.mpr hle]
  | oneMarker h a ha hf hr =>
      have hg : (localRows m hm A B).ground \ rim m hm =
          (localRows m hm A B).ground \ {«at» m hm a} := by
        rw [← residual_without_markers m hm A B, hr]
      simp only [decorated, markerNormalForm, if_pos h, hg, hE]
  | separated h hf hr apart =>
      simp only [decorated, markerNormalForm, if_pos h, hE]
  | intact ha hb hf full sole labels root =>
      have hg : (localRows m hm A B).ground = ground m := by
        simp [localRows, cornerRows, HistoryCorners.residual, ha, hb, Rows.without, rimRows]
      have hAR : Disjoint A (rim m hm) := by simp [ha]
      simp only [decorated, markerNormalForm, if_pos hAR, root, hg, tailGround]
end Markers

section PhysicalTransport
variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Injective transport of the literal FILTER-then-PROJECT indexed corner.
Reuse renameRows/renameRows_root; no second relabel engine is defined. -/
theorem corner_rows_transport (f : U ↪ V) (r : Rows U) (A B : Finset U) :
    (cornerRows (renameRows f r) (A.image f) (B.image f)).root =
      renameFamily f (cornerRows r A B).root := by
  have hg : HistoryCorners.residual (r.ground.image f) (A.image f) (B.image f) =
      (HistoryCorners.residual r.ground A B).image f := by
    rw [HistoryCorners.residual, HistoryCorners.residual, Finset.image_sdiff _ _ f.injective, Finset.image_union]
  apply SetLike.ext
  intro s
  change (∃ c : {c : r.chords // Disjoint ((r.row c).image f) (A.image f)},
    s ⊆ HistoryCorners.residual (r.ground.image f) (A.image f) (B.image f) \
      ((r.row c.1).image f \ B.image f)) ↔
    ∃ t, (∃ c : {c : r.chords // Disjoint (r.row c) A},
      t ⊆ HistoryCorners.residual r.ground A B \ (r.row c.1 \ B)) ∧ t.image f = s
  simp only [Finset.disjoint_image f.injective, hg,
    ← Finset.image_sdiff _ _ f.injective]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨t, ht, rfl⟩ := Finset.subset_image_iff.mp hc
    exact ⟨t, ⟨⟨c.1, (Finset.disjoint_image f.injective).mp c.2⟩, ht⟩, rfl⟩
  · rintro ⟨t, ⟨c, hc⟩, rfl⟩
    exact ⟨⟨c.1, (Finset.disjoint_image f.injective).mpr c.2⟩,
      Finset.image_subset_image hc⟩

/-- This is the actual physical wheel consumer: the source is its real path-row
root with precisely the interface rim row removed, not a supplied row model. -/
theorem physical_corner_transport (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)
    (A B : Finset (Label m)) (hA : A ⊆ ground m) :
    corner ((ground m).image f) (A.image f) (B.image f)
      (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root) =
      renameFamily f (localRows m hm A B).root := by
  let r := (rimRows m (by omega)).without (interfaceRow m hm)
  have hr : ((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root =
      (renameRows f r).root :=
    (PhysicalMWheel.ambient_without m hm f).trans (renameRows_root f r).symm
  rw [hr]
  change corner (renameRows f r).ground (A.image f) (B.image f) (renameRows f r).root = _
  rw [corner_root (renameRows f r) (A.image f) (B.image f)
    (Finset.image_subset_image hA), corner_rows_transport]
  rfl

/-- Every disjoint ambient local mask is read back to ORIGINAL coordinates.
The full image of the ground is preserved, even at labels absent from every face. -/
theorem physical_original_masks (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)
    (A' B' : Finset V) (hA' : A' ⊆ (ground m).image f)
    (hB' : B' ⊆ (ground m).image f) (hAB' : Disjoint A' B') :
    ∃ A B : Finset (Label m), A ⊆ ground m ∧ B ⊆ ground m ∧ Disjoint A B ∧
      A.image f = A' ∧ B.image f = B' ∧
      corner ((ground m).image f) A' B'
        (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root) =
        renameFamily f (localRows m hm A B).root := by
  obtain ⟨A, hA, rfl⟩ := Finset.subset_image_iff.mp hA'
  obtain ⟨B, hB, rfl⟩ := Finset.subset_image_iff.mp hB'
  exact ⟨A, B, hA, hB, (Finset.disjoint_image f.injective).mp hAB',
    rfl, rfl, physical_corner_transport m hm f A B hA⟩
end PhysicalTransport

section ExactPathReadback
variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

/-- Reuse the frozen path edge theorem and pathRows_mem; equality of roots does
not replace the indexed localRows presentation used by all classification data. -/
theorem local_path_root (hA : A ⊆ ground m) :
    (localRows m hm A B).root = corner (ground m) A B
      (HistoryPaths.pathRows (pathRootPath m hm)).root := by
  have hp : pathRoot m hm = (HistoryPaths.pathRows (pathRootPath m hm)).root := by
    apply SetLike.ext
    intro s
    rw [HistoryPaths.pathRows_mem, pathRootPath_vertices, pathRootPath_row_edges]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨hi.trans Finset.sdiff_subset, rimEdge m (by omega) i.1,
        Finset.mem_image.mpr ⟨i.1, Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩, rfl⟩, ?_⟩
      exact Finset.disjoint_left.mpr (fun x hx hxs => (Finset.mem_sdiff.mp (hi hxs)).2 hx)
    · rintro ⟨hs, q, hq, hdis⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      refine ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, ?_⟩
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hs hx, fun hq => Finset.disjoint_left.mp hdis hq hx⟩
  rw [← hp]
  exact (corner_root ((rimRows m (by omega)).without (interfaceRow m hm)) A B hA).symm

/-- Each derived consecutive component has exactly its consecutive path edges.
Together with component_consecutive this is a linear forest, including isolated
HistoryCorners.residual labels and the singleton constraint components. -/
theorem component_edges (a x y : Fin m)
    (hx : x ∈ component m hm A B a) (hy : y ∈ component m hm A B a) :
    (reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  constructor
  · rintro ⟨k, hk, h | h⟩ <;> omega
  · intro h
    have hxy := interval_trans m hm A B
      (interval_symm m hm A B ((mem_component m hm A B a x).mp hx).2)
      ((mem_component m hm A B a y).mp hy).2
    rcases h with h | h
    · let k : Fin (m - 1) := ⟨x.val, by have := y.isLt; omega⟩
      exact ⟨k, hxy k (by dsimp [k]; omega) (by dsimp [k]; omega),
        Or.inl ⟨rfl, h.symm⟩⟩
    · let k : Fin (m - 1) := ⟨y.val, by have := x.isLt; omega⟩
      exact ⟨k, hxy k (by dsimp [k]; omega) (by dsimp [k]; omega),
        Or.inr ⟨rfl, h.symm⟩⟩

/-- The graph edges are EXACTLY the surviving size-two indexed rows.
No graph connectivity or desired edge relation is assumed. -/
theorem graph_actual_rows (a b : Fin m) :
    (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧
      ∃ c : (prune (localRows m hm A B)).chords,
        (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b} := by
  constructor
  · rintro ⟨k, ⟨c, hc, hd⟩, hor⟩
    have hn : a ≠ b := by intro he; subst b; rcases hor with h | h <;> omega
    refine ⟨hn, ⟨c, Or.inr (by simpa only [hc] using hd)⟩, ?_⟩
    change (localRows m hm A B).row c = _
    rw [hc]
    rcases hor with h | h
    · have ha : a = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1
      have hb : b = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2
      simp [cutRow, ha, hb]
    · have hb : b = (⟨k.val, by omega⟩ : Fin m) := Fin.ext h.1
      have ha : a = (⟨k.val + 1, by omega⟩ : Fin m) := Fin.ext h.2
      simp [cutRow, ha, hb, Finset.pair_comm]
  · rintro ⟨hab, c, hc⟩
    have hne : «at» m hm a ≠ «at» m hm b := fun h => hab (at_injective m hm h)
    have hcard : ((prune (localRows m hm A B)).row c).card = 2 := by simp [hc, hne]
    rcases reduced_row_cases m hm A B c with h0 | h1 | h2
    · rw [h0, Finset.card_empty] at hcard; omega
    · obtain ⟨i, hi, he, hf⟩ := h1
      rw [he, Finset.card_singleton] at hcard; omega
    · obtain ⟨k, hk, he⟩ := h2
      have hea : «at» m hm a ∈ cutRow m hm k := by rw [← he, hc]; simp
      have heb : «at» m hm b ∈ cutRow m hm k := by rw [← he, hc]; simp
      have ha : a.val = k.val ∨ a.val = k.val + 1 := by
        rcases (show «at» m hm a = «at» m hm (⟨k.val, by omega⟩ : Fin m) ∨
          «at» m hm a = «at» m hm (⟨k.val + 1, by omega⟩ : Fin m) by
            simpa only [cutRow, Finset.mem_insert, Finset.mem_singleton] using hea) with h | h
        · exact Or.inl (congrArg Fin.val (at_injective m hm h))
        · exact Or.inr (congrArg Fin.val (at_injective m hm h))
      have hb : b.val = k.val ∨ b.val = k.val + 1 := by
        rcases (show «at» m hm b = «at» m hm (⟨k.val, by omega⟩ : Fin m) ∨
          «at» m hm b = «at» m hm (⟨k.val + 1, by omega⟩ : Fin m) by
            simpa only [cutRow, Finset.mem_insert, Finset.mem_singleton] using heb) with h | h
        · exact Or.inl (congrArg Fin.val (at_injective m hm h))
        · exact Or.inr (congrArg Fin.val (at_injective m hm h))
      have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
      exact ⟨k, hk, by omega⟩
/-- The component partition covers every retained original position. -/
theorem components_cover (a : Fin m) : a ∈ live m hm A B ↔
    ∃ C ∈ components m hm A B, a ∈ C := by
  constructor
  · intro ha
    exact ⟨component m hm A B a,
      Finset.mem_image.mpr ⟨a, ha, rfl⟩, self_component m hm A B a ha⟩
  · rintro ⟨C, hC, ha⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hC
    exact (Finset.mem_filter.mp ha).1

/-- This cover is on the ORIGINAL HistoryCorners.residual ground, not on the face support. -/
theorem original_labels (x : Label m) : x ∈ (localRows m hm A B).ground ↔
    ∃ a ∈ live m hm A B, x ∈ block m hm A B a := by
  constructor
  · intro hx
    have hxG : x ∈ ground m := (Finset.mem_sdiff.mp hx).1
    let a : Fin m := ⟨position m x, position_lt m hm x hxG⟩
    have he : «at» m hm a = x := at_position m hm x hxG
    have ha : a ∈ live m hm A B := by simp [live, he, hx]
    exact ⟨a, ha, he ▸ (block_mem m hm A B a a).mpr ⟨ha, ⟨.nil⟩⟩⟩
  · rintro ⟨a, ha, hx⟩
    exact block_supported m hm A B a hx

/-- Both original surviving markers occupy extreme positions in their blocks. -/
theorem marker_positions : markers m hm A B ⊆
    {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)} := by
  intro x hx
  have hr := (Finset.mem_inter.mp hx).1
  simpa only [at_leftEnd, at_rightEnd, rim, Finset.mem_insert, Finset.mem_singleton,
    or_comm] using hr
end ExactPathReadback

section TotalParent
variable (m : Nat) (hm : 3 ≤ m) (A B : Finset (Label m))

/-- Exhaustive row terminal state. These constructors contain facts DERIVED from
actual indices, not hypotheses passed to the structural constructor. -/
inductive RowCase : Type
  | simplex (c : (localRows m hm A B).chords) (empty : (localRows m hm A B).row c = ∅)
  | void (none : IsEmpty (localRows m hm A B).chords)
  | forest (some : Nonempty (localRows m hm A B).chords)
      (nonempty : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅)

def classifyRows : RowCase m hm A B := by
  classical
  by_cases h : ∃ c : (localRows m hm A B).chords, (localRows m hm A B).row c = ∅
  · exact .simplex (Classical.choose h) (Classical.choose_spec h)
  · have h0 : ∀ c : (localRows m hm A B).chords, (localRows m hm A B).row c ≠ ∅ :=
      fun c hc => h ⟨c, hc⟩
    by_cases hI : Nonempty (localRows m hm A B).chords
    · exact .forest hI h0
    · exact .void ⟨fun c => hI ⟨c⟩⟩

/-- Raw local root for every computed row state, including zero-ground VOID/UNIT. -/
def rowRootForm : RowCase m hm A B → Family (Label m)
  | .simplex _ _ => delta (localRows m hm A B).ground
  | .void _ => ⊥
  | .forest _ _ => componentUnion m hm A B

private theorem row_root_readback : (localRows m hm A B).root =
    rowRootForm m hm A B (classifyRows m hm A B) := by
  generalize he : classifyRows m hm A B = c
  cases c with
  | simplex c hc => exact empty_row_root _ c hc
  | void h => exact no_rows_root _ h
  | forest hI h0 => exact component_root m hm A B h0

/-- An empty local row gives the entire parent simplex; the old factors have
only support hypotheses. No simplex/Output assertion is supplied as a premise. -/
private theorem decorated_simplex {V : Type*} [Fintype V] [DecidableEq V]
    (f : Label m ↪ V) (X : Finset V) (D L : Family V)
    (hD : Supported X D) (hLD : L ≤ D)
    (c : (localRows m hm A B).chords) (hc : (localRows m hm A B).row c = ∅) :
    decorated m hm A B f X D L = delta (X ∪ (localRows m hm A B).ground.image f) := by
  have hE : renameFamily f (localRows m hm A B).root =
      delta ((localRows m hm A B).ground.image f) := by
    rw [empty_row_root _ c hc]
    exact (rename_operations f (localRows m hm A B).ground (delta ∅) (delta ∅) ∅).1
  have hDU : (((localRows m hm A B).ground \ rim m hm).image f) ⊆
      (localRows m hm A B).ground.image f := Finset.image_subset_image Finset.sdiff_subset
  apply SetLike.ext
  intro s
  constructor
  · intro hs
    change s ∈ (rawJoin (delta X) (renameFamily f (localRows m hm A B).root) ⊔
      rawJoin L (delta ((localRows m hm A B).ground.image f))) ⊔
      (if Disjoint A (rim m hm) then rawJoin D
        (delta (((localRows m hm A B).ground \ rim m hm).image f)) else ⊥) at hs
    rw [hE] at hs
    rcases hs with (⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩) | hs
    · exact Finset.union_subset_union hu hv
    · exact Finset.union_subset_union (hD u (hLD hu)) hv
    · by_cases h : Disjoint A (rim m hm)
      · rw [if_pos h] at hs
        obtain ⟨u, hu, v, hv, rfl⟩ := hs
        exact Finset.union_subset_union (hD u hu) (hv.trans hDU)
      · rw [if_neg h] at hs
        exact hs.elim
  · intro hs
    apply Or.inl
    apply Or.inl
    rw [hE]
    refine ⟨s ∩ X, Finset.inter_subset_right,
      s ∩ (localRows m hm A B).ground.image f, Finset.inter_subset_right, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp (hs hx) with hxX | hxU
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxX⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxU⟩)
    · simp only [Finset.mem_union, Finset.mem_inter]; tauto

/-- Total parent normal form, including the empty-row simplex branch. -/
def parentNormalForm {V : Type*} [Fintype V] [DecidableEq V]
    (f : Label m ↪ V) (X : Finset V) (D L : Family V)
    (r : RowCase m hm A B) (c : MarkerCase m hm A B) : Family V :=
  match r with
  | .simplex _ _ => delta (X ∪ (localRows m hm A B).ground.image f)
  | .void _ => markerNormalForm m hm A B f X D L c
  | .forest _ _ => markerNormalForm m hm A B f X D L c

private theorem total_parent_readback {V : Type*} [Fintype V] [DecidableEq V]
    (hA : A ⊆ ground m) (hB : B ⊆ ground m)
    (f : Label m ↪ V) (X : Finset V) (D L : Family V)
    (hD : Supported X D) (hLD : L ≤ D) :
    decorated m hm A B f X D L = parentNormalForm m hm A B f X D L
      (classifyRows m hm A B) (classifyMarkers m hm A B hA hB) := by
  generalize he : classifyRows m hm A B = r
  cases r with
  | simplex c hc => exact decorated_simplex m hm A B f X D L hD hLD c hc
  | void h =>
      exact decorated_readback m hm A B hA hB
        (fun c => (h.false c).elim) f X D L hD hLD
  | forest hi h0 => exact decorated_readback m hm A B hA hB h0 f X D L hD hLD

/-- Exact structural result on actual masks. All geometry fields are conclusions
of parentStructure. The record contains no native certificate or deformation. -/
structure ParentStructure {V : Type*} [Fintype V] [DecidableEq V]
    (f : Label m ↪ V) (X : Finset V) (D L : Family V) where
  rowState : RowCase m hm A B
  markerState : MarkerCase m hm A B
  localRoot : (localRows m hm A B).root = rowRootForm m hm A B rowState
  parentRoot : decorated m hm A B f X D L = parentNormalForm m hm A B f X D L rowState markerState
  literalPath : (localRows m hm A B).root = corner (ground m) A B
    (HistoryPaths.pathRows (pathRootPath m hm)).root
  cover : ∀ a : Fin m, a ∈ live m hm A B ↔ ∃ C ∈ components m hm A B, a ∈ C
  originalGround : ∀ x : Label m, x ∈ (localRows m hm A B).ground ↔
    ∃ a ∈ live m hm A B, x ∈ block m hm A B a
  originalMarkers : markers m hm A B ⊆ {«at» m hm (leftEnd m hm), «at» m hm (rightEnd m hm)}
  graphRows : ∀ a b : Fin m, (reducedGraph m hm A B).Adj a b ↔ a ≠ b ∧
    ∃ c : (prune (localRows m hm A B)).chords,
      (prune (localRows m hm A B)).row c = {«at» m hm a, «at» m hm b}
  partition : ∀ a b : Fin m, a ∈ live m hm A B → b ∈ live m hm A B →
    component m hm A B a = component m hm A B b ∨
      Disjoint (component m hm A B a) (component m hm A B b)
  consecutive : ∀ a x y z : Fin m, x ∈ component m hm A B a →
    y ∈ component m hm A B a → x.val ≤ z.val → z.val ≤ y.val → z ∈ component m hm A B a
  componentPaths : ∀ a x y : Fin m, x ∈ component m hm A B a → y ∈ component m hm A B a →
    ((reducedGraph m hm A B).Adj x y ↔ x.val + 1 = y.val ∨ y.val + 1 = x.val)
  forcedSingletons : ∀ a : Fin m, a ∈ live m hm A B →
    «at» m hm a ∈ forced (localRows m hm A B) → component m hm A B a = {a}
  isolatedGhosts : ∀ a : Fin m, a ∈ live m hm A B →
    (∀ b, ¬ (reducedGraph m hm A B).Adj a b) → component m hm A B a = {a}
  separatedEnds : leftEnd m hm ∈ live m hm A B → rightEnd m hm ∈ live m hm A B →
    ¬ Nonempty ((reducedGraph m hm A B).Walk (leftEnd m hm) (rightEnd m hm)) →
    Disjoint (component m hm A B (leftEnd m hm)) (component m hm A B (rightEnd m hm))

/-- The genuinely consumed constructor. Every caller supplies only ORIGINAL masks,
injection, earlier families and their support/order, never a desired structural result. -/
def parentStructure {V : Type*} [Fintype V] [DecidableEq V]
    (hA : A ⊆ ground m) (hB : B ⊆ ground m)
    (f : Label m ↪ V) (X : Finset V) (D L : Family V)
    (hD : Supported X D) (hLD : L ≤ D) : ParentStructure m hm A B f X D L where
  rowState := classifyRows m hm A B
  markerState := classifyMarkers m hm A B hA hB
  localRoot := row_root_readback m hm A B
  parentRoot := total_parent_readback m hm A B hA hB f X D L hD hLD
  literalPath := local_path_root m hm A B hA
  cover := components_cover m hm A B
  originalGround := original_labels m hm A B
  originalMarkers := marker_positions m hm A B
  graphRows := graph_actual_rows m hm A B
  partition := component_partition m hm A B
  consecutive := component_consecutive m hm A B
  componentPaths := component_edges m hm A B
  forcedSingletons := forced_component m hm A B
  isolatedGhosts := isolated_component m hm A B
  separatedEnds := separated_components m hm A B
end TotalParent

section PhysicalParent
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The physical source corner, at arbitrary ambient original masks. -/
def physicalDecorated (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)
    (A B X : Finset V) (D L : Family V) : Family V :=
  let U := HistoryCorners.residual ((ground m).image f) A B
  (rawJoin (delta X) (corner ((ground m).image f) A B
    (((PhysicalMWheel.ambientGraph m hm f).rows.without (interfaceRow m hm)).root)) ⊔
    rawJoin L (delta U)) ⊔
    if Disjoint A ((rim m hm).image f) then rawJoin D (delta (U \ (rim m hm).image f)) else ⊥

/-- Final total physical consumer: masks are pulled back from the REAL ambient
wheel ground, the literal physical corner is identified, and its exact parent
factor receives the computed structural normal form. This proves no strong Output. -/
theorem physical_parent_readback (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V)
    (A' B' X : Finset V) (D L : Family V)
    (hA' : A' ⊆ (ground m).image f) (hB' : B' ⊆ (ground m).image f)
    (hAB' : Disjoint A' B') (hD : Supported X D) (hLD : L ≤ D) :
    ∃ (A B : Finset (Label m)) (hA : A ⊆ ground m) (hB : B ⊆ ground m),
      Disjoint A B ∧ A.image f = A' ∧ B.image f = B' ∧
      ∃ s : ParentStructure m hm A B f X D L,
        physicalDecorated m hm f A' B' X D L =
          parentNormalForm m hm A B f X D L s.rowState s.markerState := by
  obtain ⟨A, B, hA, hB, hAB, hAi, hBi, hcorner⟩ :=
    physical_original_masks m hm f A' B' hA' hB' hAB'
  let s := parentStructure m hm A B hA hB f X D L hD hLD
  refine ⟨A, B, hA, hB, hAB, hAi, hBi, s, ?_⟩
  have hground : HistoryCorners.residual ((ground m).image f) A' B' =
      (localRows m hm A B).ground.image f := by
    rw [← hAi, ← hBi]
    change HistoryCorners.residual ((ground m).image f) (A.image f) (B.image f) = (HistoryCorners.residual (ground m) A B).image f
    rw [HistoryCorners.residual, HistoryCorners.residual, Finset.image_sdiff _ _ f.injective, Finset.image_union]
  have hswitch : Disjoint A' ((rim m hm).image f) ↔ Disjoint A (rim m hm) := by
    rw [← hAi]
    exact Finset.disjoint_image f.injective
  have hphysical : physicalDecorated m hm f A' B' X D L = decorated m hm A B f X D L := by
    simp only [physicalDecorated, decorated, hcorner, hground, hswitch,
      Finset.image_sdiff _ _ f.injective]
  exact hphysical.trans s.parentRoot
end PhysicalParent

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
