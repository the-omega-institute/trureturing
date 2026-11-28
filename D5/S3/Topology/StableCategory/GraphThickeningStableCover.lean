/- GID: D5/S3/Topology/StableCategory/GraphThickeningStableCover
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/GraphThickeningStableCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first subdivision of a graph thickening has a categorical lower two-cover. -/

import D5.S3.Topology.StableCategory.MaximalChainCoverExtension
import D5.S3.Topology.SubdivisionCategoricalCover
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite

/-!
# A two-cover of the first ordinary subdivision of the graph thickening

This realizes the upper bound in Sections 1–2 and 4 of
`graph-thickening-review.txt` for Question 6.3 of
https://arxiv.org/html/2609.39615v1#S6.Thmtheorem3.
The local compiled dependency is the module from
`MaximalChainCoverExtension.checked.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.GraphThickeningStableCover

open D5.S3.Topology.ConnectedCategoryGraft (Categorical HasCategoricalCover)
open D5.S3.Topology.SubdivisionCategoricalCover (subdivision_map_fence)
open MaximalChainCoverExtension (chainsAvoiding exists_relative_two_cover_of_maximal_lower_chains)
open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open Relation (EqvGen)
open scoped Classical

variable {V : Type*} (G : SimpleGraph V)

/-- An edge is an unordered pair of adjacent vertices. -/
abbrev Edge := ↥(G.edgeSet)

/-- The apex, original vertices, and one subdivision vertex per unordered edge. -/
abbrev Vertex := Option (V ⊕ Edge G)

def apex : Vertex G := none
def original (u : V) : Vertex G := some (Sum.inl u)
def midpoint (e : Edge G) : Vertex G := some (Sum.inr e)

/-- Use the two coordinates of a representative of the unordered pair only
to label the two sides. The edge itself remains an element of `G.edgeSet`. -/
def endpoint (e : Edge G) (i : Fin 2) : V :=
  if i = 0 then (e : Sym2 V).out.1 else (e : Sym2 V).out.2

theorem endpoint_pair (e : Edge G) :
    Sym2.mk (endpoint G e 0) (endpoint G e 1) = (e : Sym2 V) := by
  simpa [endpoint] using Sym2.mk_fst_out_snd_out (e : Sym2 V)

theorem endpoint_ne (e : Edge G) : endpoint G e 0 ≠ endpoint G e 1 := by
  intro h
  have hd : (Sym2.mk (endpoint G e 0) (endpoint G e 1)).IsDiag :=
    Sym2.mk_isDiag_iff.mpr h
  rw [endpoint_pair G e] at hd
  exact G.not_isDiag_of_mem_edgeSet e.property hd

/-- The two sides have vertex sets `{u, x_e}` and `{v, x_e}`. -/
def side (e : Edge G) (i : Fin 2) : Finset (Vertex G) :=
  {original G (endpoint G e i), midpoint G e}

/-- The vertex set coding the new maximum over the two sides of an edge. -/
def cap (e : Edge G) : Finset (Vertex G) :=
  {original G (endpoint G e 0), midpoint G e, original G (endpoint G e 1)}

/-- All faces of the once-subdivided graph, including the empty face and
isolated original vertices. The graph is regarded as one-dimensional. -/
def IsSubdividedFace (s : Finset (Vertex G)) : Prop :=
  s = ∅ ∨ (∃ u : V, s ⊆ {original G u}) ∨
    ∃ (e : Edge G) (i : Fin 2), s ⊆ side G e i

/-- The cone faces are obtained by allowing the apex in every subdivided face. -/
def IsConeFace (s : Finset (Vertex G)) : Prop :=
  IsSubdividedFace G (s.erase (apex G))

private theorem coneFace_mono {s t : Finset (Vertex G)} (hst : s ⊆ t)
    (ht : IsConeFace G t) : IsConeFace G s := by
  have h := Finset.erase_subset_erase (apex G) hst
  unfold IsConeFace IsSubdividedFace at ht ⊢
  rcases ht with h0 | ⟨u, hu⟩ | ⟨e, i, he⟩
  · exact Or.inl (Finset.subset_empty.mp (h0 ▸ h))
  · exact Or.inr (Or.inl ⟨u, h.trans hu⟩)
  · exact Or.inr (Or.inr ⟨e, i, h.trans he⟩)

/-- Inclusion of vertex sets orders the nonempty cone faces and the added caps.
Only the full triple of each cap is adjoined to the cone part. -/
abbrev P_G :=
  {s : Finset (Vertex G) // s.Nonempty ∧ (IsConeFace G s ∨ ∃ e : Edge G, s = cap G e)}

instance [Finite V] : Finite (P_G G) := by
  letI : Fintype (Vertex G) := Fintype.ofFinite (Vertex G)
  exact Finite.of_injective Subtype.val Subtype.val_injective

private theorem cap_nonempty (e : Edge G) : (cap G e).Nonempty :=
  ⟨midpoint G e, by simp [cap]⟩

/-- The element of the thickening indexed by the unordered edge `e`. -/
def newMaximum (e : Edge G) : P_G G :=
  ⟨cap G e, cap_nonempty G e, Or.inr ⟨e, rfl⟩⟩

private theorem cap_subset_cap_iff (e f : Edge G) : cap G e ⊆ cap G f ↔ e = f := by
  constructor
  · intro h
    have hm : midpoint G e ∈ cap G f := h (by simp [cap])
    simpa [cap, original, midpoint] using hm
  · rintro rfl
    exact Finset.Subset.rfl

private theorem side_subset_cap (e : Edge G) (i : Fin 2) : side G e i ⊆ cap G e := by
  have hu : original G (endpoint G e i) ∈ cap G e := by
    by_cases hi : i = 0
    · subst i
      simp [cap]
    · have hv : endpoint G e i = endpoint G e 1 := by simp [endpoint, hi]
      simp [cap, hv]
  unfold side
  refine Finset.insert_subset hu ?_
  intro x hx
  rw [Finset.mem_singleton.mp hx]
  simp [cap]

private theorem cap_not_subset_side (e : Edge G) (i : Fin 2) : ¬ cap G e ⊆ side G e i := by
  intro h
  have hl : original G (endpoint G e 0) ∈ side G e i := h (by simp [cap])
  have hr : original G (endpoint G e 1) ∈ side G e i := h (by simp [cap])
  have hl' : endpoint G e 0 = endpoint G e i := by
    simpa [side, original, midpoint] using hl
  have hr' : endpoint G e 1 = endpoint G e i := by
    simpa [side, original, midpoint] using hr
  exact endpoint_ne G e (hl'.trans hr'.symm)

private theorem cone_subset_cap_has_side (e : Edge G) {s : Finset (Vertex G)}
    (hs : s.Nonempty) (hc : IsConeFace G s) (hcap : s ⊆ cap G e) :
    ∃ i : Fin 2, s ⊆ side G e i := by
  have hapex : apex G ∉ s := fun ha =>
    (show apex G ∉ cap G e by simp [cap, apex, original, midpoint]) (hcap ha)
  have hsingleton (u : V) (hu : s ⊆ {original G u}) :
      ∃ i : Fin 2, s ⊆ side G e i := by
    obtain ⟨x, hx⟩ := hs
    have hx' : x = original G u := Finset.mem_singleton.mp (hu hx)
    have hmem : original G u ∈ cap G e := hx' ▸ hcap hx
    have hend : u = endpoint G e 0 ∨ u = endpoint G e 1 := by
      simpa [cap, original, midpoint] using hmem
    rcases hend with h0 | h1
    · exact ⟨0, fun y hy => by simp [side, Finset.mem_singleton.mp (hu hy), h0]⟩
    · exact ⟨1, fun y hy => by simp [side, Finset.mem_singleton.mp (hu hy), h1]⟩
  unfold IsConeFace at hc
  rw [Finset.erase_eq_of_notMem hapex] at hc
  unfold IsSubdividedFace at hc
  rcases hc with h0 | ⟨u, hu⟩ | ⟨f, i, hf⟩
  · exact (Finset.not_nonempty_empty (h0 ▸ hs)).elim
  · exact hsingleton u hu
  · by_cases hm : midpoint G f ∈ s
    · have hmid : midpoint G f ∈ cap G e := hcap hm
      have hfe : f = e := by simpa [cap, original, midpoint] using hmid
      exact ⟨i, hfe ▸ hf⟩
    · apply hsingleton (endpoint G f i)
      intro x hx
      have hxSide := hf hx
      change x ∈ insert (original G (endpoint G f i)) {midpoint G f} at hxSide
      rcases Finset.mem_insert.mp hxSide with h | h
      · exact Finset.mem_singleton.mpr h
      · exact (hm (Finset.mem_singleton.mp h ▸ hx)).elim

private theorem cap_not_cone (e : Edge G) : ¬ IsConeFace G (cap G e) := by
  intro h
  obtain ⟨i, hi⟩ := cone_subset_cap_has_side G e (cap_nonempty G e) h Finset.Subset.rfl
  exact cap_not_subset_side G e i hi

/-- The range of the added points. Cone faces can also be maximal in `P_G`. -/
def newMaxima : Set (P_G G) := Set.range (newMaximum G)

theorem newMaximum_le_iff (e f : Edge G) :
    newMaximum G e ≤ newMaximum G f ↔ e = f :=
  cap_subset_cap_iff G e f

/-- Exactly one distinct new maximum for each edge in Mathlib's graph. -/
def edgeEquivNewMaxima : Edge G ≃ newMaxima G :=
  Equiv.ofInjective (newMaximum G) (fun e f h =>
    (newMaximum_le_iff G e f).mp h.le)

@[simp]
theorem edgeEquivNewMaxima_val (e : Edge G) :
    (edgeEquivNewMaxima G e).val = newMaximum G e := rfl

theorem newMaximum_isMax (e : Edge G) : IsMax (newMaximum G e) := by
  intro y h
  rcases y.property.2 with hold | ⟨f, hf⟩
  · exact (cap_not_cone G e (coneFace_mono G h hold)).elim
  · have hsub : cap G e ⊆ cap G f := by
      change cap G e ⊆ y.val at h
      rwa [hf] at h
    have hef := (cap_subset_cap_iff G e f).mp hsub
    have hy : y = newMaximum G f := Subtype.ext hf
    exact (hy.trans (congrArg (newMaximum G) hef.symm)).le

private theorem newMaxima_isMax (x : P_G G) (hx : x ∈ newMaxima G) : IsMax x := by
  obtain ⟨e, rfl⟩ := hx
  exact newMaximum_isMax G e

/-- The face poset of the subdivided cone as a lower subposet of `P_G`. -/
def ConePart : Set (P_G G) := {x | IsConeFace G x.val}

theorem mem_conePart_iff (x : P_G G) : x ∈ ConePart G ↔ x ∉ newMaxima G := by
  constructor
  · rintro h ⟨e, he⟩
    have hc : IsConeFace G x.val := h
    rw [← he] at hc
    exact cap_not_cone G e hc
  · intro hx
    rcases x.property.2 with hold | ⟨e, he⟩
    · exact hold
    · exact (hx ⟨e, Subtype.ext he.symm⟩).elim

theorem conePart_lower : IsLowerSet (ConePart G) :=
  fun _ _ h hold => coneFace_mono G h hold

/-- The edge face of one of the two sides below the cap. -/
def pathFace (e : Edge G) (i : Fin 2) : P_G G := by
  refine ⟨side G e i, ⟨midpoint G e, by simp [side]⟩, Or.inl ?_⟩
  unfold IsConeFace IsSubdividedFace
  exact Or.inr (Or.inr ⟨e, i, Finset.erase_subset _ _⟩)

theorem pathFace_lt (e : Edge G) (i : Fin 2) : pathFace G e i < newMaximum G e :=
  lt_of_le_not_ge (side_subset_cap G e i) (cap_not_subset_side G e i)

/-- The strict lower set is exactly the nonempty face poset of the path
`u – x_e – v`. Its two principal ideals are generated by the two edge faces. -/
theorem lt_newMaximum_iff (x : P_G G) (e : Edge G) :
    x < newMaximum G e ↔ ∃ i : Fin 2, x ≤ pathFace G e i := by
  constructor
  · intro h
    have hcap : x.val ⊆ cap G e := h.le
    rcases x.property.2 with hc | ⟨f, hf⟩
    · exact cone_subset_cap_has_side G e x.property.1 hc hcap
    · have hfe : f = e := (cap_subset_cap_iff G f e).mp (hf ▸ hcap)
      have hxe : x = newMaximum G e := Subtype.ext (hf.trans (congrArg (cap G) hfe))
      exact (h.ne hxe).elim
  · rintro ⟨i, hi⟩
    exact hi.trans_lt (pathFace_lt G e i)

private def coneApex : ConePart G := by
  have h : IsConeFace G ({apex G} : Finset (Vertex G)) := by
    unfold IsConeFace IsSubdividedFace
    exact Or.inl (by simp)
  exact ⟨⟨{apex G}, Finset.singleton_nonempty _, Or.inl h⟩, h⟩

private theorem insert_apex_isConeFace (x : ConePart G) :
    IsConeFace G (insert (apex G) x.val.val) := by
  unfold IsConeFace
  rw [Finset.erase_insert_eq_erase]
  exact x.property

/-- Add the apex to a cone face, retaining all of its other vertices. -/
def addApex : ConePart G →o ConePart G where
  toFun x := ⟨⟨insert (apex G) x.val.val, ⟨apex G, Finset.mem_insert_self _ _⟩,
    Or.inl (insert_apex_isConeFace G x)⟩, insert_apex_isConeFace G x⟩
  monotone' := by
    intro x y h
    change x.val.val ⊆ y.val.val at h
    change insert (apex G) x.val.val ⊆ insert (apex G) y.val.val
    exact Finset.insert_subset_insert _ h

/-- On cone faces the identity and the constant apex map both lie below
the map that adjoins the apex. -/
theorem conePart_contraction :
    EqvGen (· ≤ ·) (OrderHom.id : ConePart G →o ConePart G)
      (OrderHom.const (ConePart G) (coneApex G)) := by
  have hup : (OrderHom.id : ConePart G →o ConePart G) ≤ addApex G := by
    intro x
    change x.val.val ⊆ insert (apex G) x.val.val
    exact Finset.subset_insert _ _
  have hdown : OrderHom.const (ConePart G) (coneApex G) ≤ addApex G := by
    intro x y hy
    change y ∈ ({apex G} : Finset (Vertex G)) at hy
    change y ∈ insert (apex G) x.val.val
    rw [Finset.mem_singleton.mp hy]
    exact Finset.mem_insert_self _ _
  exact .trans _ _ _ (.rel _ _ hup) (.symm _ _ (.rel _ _ hdown))

/-- The common region in the first ordinary subdivision, the nonempty
chains of cone faces viewed inside the full chain poset. -/
def D : Set (NonemptyFiniteChains (P_G G)) := chainsAvoiding (newMaxima G)

theorem D_lower : IsLowerSet (D G) :=
  fun _ _ h hs x hx => hs x (h hx)

private def restrictConeChains : D G →o NonemptyFiniteChains (ConePart G) where
  toFun s := {
    finset := s.val.finset.subtype (· ∈ ConePart G)
    nonempty := by
      obtain ⟨x, hx⟩ := s.val.nonempty
      exact ⟨⟨x, (mem_conePart_iff G x).mpr (s.property x hx)⟩, Finset.mem_subtype.mpr hx⟩
    comparable := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      exact s.val.comparable ⟨x.val, Finset.mem_subtype.mp hx⟩
        ⟨y.val, Finset.mem_subtype.mp hy⟩ }
  monotone' _ _ h := Finset.subtype_mono h

private def coneInclusion : ConePart G →o P_G G := (OrderEmbedding.subtype _).toOrderHom

private def includeConeChains : NonemptyFiniteChains (ConePart G) →o D G where
  toFun s := ⟨s.map (coneInclusion G), by
    intro x hx
    obtain ⟨y, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hx
    exact (mem_conePart_iff G y.val).mp y.property⟩
  monotone' _ _ h := (orderHomMap (coneInclusion G)).monotone h

private theorem include_restrict (s : D G) :
    includeConeChains G (restrictConeChains G s) = s := by
  apply Subtype.ext
  apply NonemptyFiniteChains.ext
  apply Finset.ext
  intro x
  change x ∈ ((restrictConeChains G s).map (coneInclusion G)).finset ↔ x ∈ s.val.finset
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Finset.mem_subtype.mp hy
  · intro hx
    exact ⟨⟨x, (mem_conePart_iff G x).mpr (s.property x hx)⟩, Finset.mem_subtype.mpr hx, rfl⟩

private def singletonChain {X : Type*} [PartialOrder X] (a : X) : NonemptyFiniteChains X :=
  ⟨{a}, Finset.singleton_nonempty a, by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    change x ≤ y ∨ y ≤ x
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
    exact Or.inl le_rfl⟩

private theorem mapFence {X Y : Type*} [Preorder X] [Preorder Y] {f : X → Y}
    (hf : Monotone f) {x y : X} (h : EqvGen (· ≤ ·) x y) :
    EqvGen (· ≤ ·) (f x) (f y) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (hf h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Ordinary contractibility of the common old region, with every map in
the fence taking values in that region. -/
theorem D_contractible [Finite V] :
    ∃ a : D G, EqvGen (· ≤ ·) (OrderHom.id : D G →o D G) (OrderHom.const (D G) a) := by
  let Chain := NonemptyFiniteChains (ConePart G)
  let a : Chain := singletonChain (coneApex G)
  have hid : orderHomMap (OrderHom.id : ConePart G →o ConePart G) =
      (OrderHom.id : Chain →o Chain) := by
    apply OrderHom.ext
    funext s
    apply NonemptyFiniteChains.ext
    exact Finset.image_id
  have hconst : orderHomMap (OrderHom.const (ConePart G) (coneApex G)) =
      OrderHom.const Chain a := by
    apply OrderHom.ext
    funext s
    apply NonemptyFiniteChains.ext
    change (s.finset.image fun _ => coneApex G) = {coneApex G}
    exact Finset.image_const s.nonempty _
  have h := subdivision_map_fence (conePart_contraction G)
  rw [hid, hconst] at h
  let lift (f : Chain →o Chain) : D G →o D G :=
    (includeConeChains G).comp (f.comp (restrictConeChains G))
  have hlift : Monotone lift := fun _ _ hfg s =>
    (includeConeChains G).monotone ((OrderHom.le_def.mp hfg) (restrictConeChains G s))
  have hstart : lift (OrderHom.id : Chain →o Chain) = OrderHom.id := by
    apply OrderHom.ext
    funext s
    exact include_restrict G s
  have hend : lift (OrderHom.const Chain a) =
      OrderHom.const (D G) (includeConeChains G a) := rfl
  have hD := mapFence hlift h
  rw [hstart, hend] at hD
  exact ⟨includeConeChains G a, hD⟩

private theorem D_categorical [Finite V] : Categorical (D G) := by
  obtain ⟨a, ha⟩ := D_contractible G
  let incl : D G →o NonemptyFiniteChains (P_G G) := (OrderEmbedding.subtype (D G)).toOrderHom
  have hmono : Monotone (fun f : D G →o D G => incl.comp f) :=
    fun _ _ hfg s => incl.monotone ((OrderHom.le_def.mp hfg) s)
  have h := mapFence hmono ha
  change EqvGen (· ≤ ·) incl (OrderHom.const (D G) (incl a)) at h
  exact ⟨incl a, h⟩

private def chosenSide (i : Fin 2) (t : newMaxima G) : P_G G :=
  pathFace G ((edgeEquivNewMaxima G).symm t) i

private theorem edgeOfMaximum_spec (t : newMaxima G) :
    newMaximum G ((edgeEquivNewMaxima G).symm t) = t.val :=
  congrArg (fun s : newMaxima G => s.val) ((edgeEquivNewMaxima G).apply_symm_apply t)

private theorem chosenSide_lt (i : Fin 2) (t : newMaxima G) : chosenSide G i t < t.val := by
  unfold chosenSide
  rw [← edgeOfMaximum_spec G t]
  exact pathFace_lt G _ i

private theorem maximal_lower_chain_hits_side (t : newMaxima G)
    (M : NonemptyFiniteChains (P_G G))
    (hM : Maximal (fun N : NonemptyFiniteChains (P_G G) => ∀ x ∈ N.finset, x < t.val) M) :
    ∃ i : Fin 2, M ∈ D G ∧ chosenSide G i t ∈ M.finset := by
  have hold : M ∈ D G := by
    intro x hx hxTop
    have hlt := hM.1 x hx
    exact (not_le_of_gt hlt) (newMaxima_isMax G x hxTop hlt.le)
  obtain ⟨m, hm⟩ := M.finset.exists_maximal M.nonempty
  have htop (x : P_G G) (hx : x ∈ M.finset) : x ≤ m :=
    (M.comparable ⟨x, hx⟩ ⟨m, hm.1⟩).elim id (fun h => hm.2 hx h)
  have hmt : m < newMaximum G ((edgeEquivNewMaxima G).symm t) := by
    rw [edgeOfMaximum_spec G t]
    exact hM.1 m hm.1
  obtain ⟨i, hmi⟩ := (lt_newMaximum_iff G m _).mp hmt
  let c := chosenSide G i t
  have hle (x : P_G G) (hx : x ∈ M.finset) : x ≤ c := (htop x hx).trans hmi
  let N : NonemptyFiniteChains (P_G G) :=
    ⟨insert c M.finset, ⟨c, Finset.mem_insert_self _ _⟩, by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      change x ≤ y ∨ y ≤ x
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inl le_rfl
        · exact Or.inr (hle y hy)
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inl (hle x hx)
        · exact M.comparable ⟨x, hx⟩ ⟨y, hy⟩⟩
  have hN (x : P_G G) (hx : x ∈ N.finset) : x < t.val := by
    change x ∈ insert c M.finset at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact chosenSide_lt G i t
    · exact hM.1 x hx
  have hMN : M ≤ N := Finset.subset_insert c M.finset
  have hcN : c ∈ N.finset := Finset.mem_insert_self c M.finset
  have hNM : N ≤ M := hM.2 hN hMN
  exact ⟨i, hold, hNM hcN⟩

/-- Two categorical lower sets cover the first ordinary subdivision.
Both extend the same old region by the maximal-lower-chain criterion. -/
theorem hasCategoricalCover_first_subdivision [Finite V] :
    HasCategoricalCover (NonemptyFiniteChains (P_G G)) 2 := by
  obtain ⟨A, hA, _, _⟩ := exists_relative_two_cover_of_maximal_lower_chains
    (newMaxima_isMax G) (fun _ => D G) (fun _ => ⟨D_lower G, D_categorical G⟩)
    (fun _ _ hs => hs) (fun _ hs => ⟨0, hs⟩)
    (chosenSide G) (chosenSide_lt G) (maximal_lower_chain_hits_side G)
  exact ⟨A, hA⟩

end D5.S3.Topology.StableCategory.GraphThickeningStableCover
