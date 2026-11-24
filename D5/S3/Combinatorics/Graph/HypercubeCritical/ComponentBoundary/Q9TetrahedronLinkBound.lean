/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Capped tetrahedral supports have at least six facets at every used vertex. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriangleSmallSupport
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.ByContra

/-! Vertex links of tetrahedral supports with no singleton three-face incidence. -/

set_option autoImplicit false

namespace Q9TriangleSupportReduction

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- The vertices occurring in the family. -/
def support (C : Finset (Finset V)) : Finset V := C.biUnion id

/-- The faces containing the vertex `v`. -/
def incident (C : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  C.filter fun t => v ∈ t

/-- The faces incident to `v`, with `v` erased from each face. -/
def link (C : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (incident C v).image fun t => t.erase v

def NoSingletonEdges (C : Finset (Finset V)) : Prop :=
  ∀ e : Finset V, e.card = 2 → (C.filter (e ⊆ ·)).card ≠ 1

private theorem mem_support {C : Finset (Finset V)} {v : V} :
    v ∈ support C ↔ ∃ t ∈ C, v ∈ t := by
  simp only [support, Finset.mem_biUnion, id_eq]

private theorem subset_support {C : Finset (Finset V)} {t : Finset V} (ht : t ∈ C) :
    t ⊆ support C :=
  fun _ hx => mem_support.mpr ⟨t, ht, hx⟩

private theorem mem_incident {C : Finset (Finset V)} {v : V} {t : Finset V} :
    t ∈ incident C v ↔ t ∈ C ∧ v ∈ t :=
  Finset.mem_filter

private theorem mem_link {C : Finset (Finset V)} {v : V} {e : Finset V} :
    e ∈ link C v ↔ v ∉ e ∧ insert v e ∈ C := by
  unfold link
  constructor
  · intro he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨htC, hvt⟩ := mem_incident.mp ht
    exact ⟨Finset.notMem_erase _ _, by simpa only [Finset.insert_erase hvt] using htC⟩
  · rintro ⟨hve, heC⟩
    exact Finset.mem_image.mpr
      ⟨insert v e, mem_incident.mpr ⟨heC, Finset.mem_insert_self _ _⟩,
        Finset.erase_insert hve⟩

private theorem card_link (C : Finset (Finset V)) (v : V) :
    (link C v).card = (incident C v).card := by
  unfold link
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  have hvs := (mem_incident.mp (Finset.mem_coe.mp hs)).2
  have hvt := (mem_incident.mp (Finset.mem_coe.mp ht)).2
  calc
    s = insert v (s.erase v) := (Finset.insert_erase hvs).symm
    _ = insert v (t.erase v) := congrArg (insert v) hst
    _ = t := Finset.insert_erase hvt

private theorem link_filter_card {C : Finset (Finset V)} {v : V} {r : Finset V}
    (hvr : v ∉ r) :
    ((link C v).filter (r ⊆ ·)).card = (incident (C.filter (r ⊆ ·)) v).card := by
  have hFilter : (link C v).filter (r ⊆ ·) = link (C.filter (r ⊆ ·)) v := by
    ext e
    simp only [Finset.mem_filter, mem_link, Finset.subset_insert_iff_of_notMem hvr]
    exact ⟨fun ⟨⟨hve, heC⟩, hre⟩ => ⟨hve, heC, hre⟩,
      fun ⟨hve, heC, hre⟩ => ⟨⟨hve, heC⟩, hre⟩⟩
  rw [hFilter, card_link]

private theorem two_le_link_degree {C : Finset (Finset V)} {v x : V}
    (hNo : NoSingletonEdges C) (hx : x ∈ support (link C v)) :
    2 ≤ (incident (link C v) x).card := by
  obtain ⟨t, ht, hxt⟩ := mem_support.mp hx
  have hxv : v ∉ ({x} : Finset V) :=
    fun hv => (mem_link.mp ht).1 ((Finset.singleton_subset_iff.mpr hxt) hv)
  have hCount := link_filter_card (C := C) hxv
  have hCofaces : incident (C.filter (({x} : Finset V) ⊆ ·)) v =
      C.filter (insert v ({x} : Finset V) ⊆ ·) := by
    ext s
    simp only [incident, Finset.mem_filter, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨fun ⟨⟨hs, hxs⟩, hvs⟩ => ⟨hs, hvs, hxs⟩,
      fun ⟨hs, hvs, hxs⟩ => ⟨⟨hs, hxs⟩, hvs⟩⟩
  rw [hCofaces] at hCount
  simp only [Finset.singleton_subset_iff] at hCount
  change (incident (link C v) x).card = _ at hCount
  have hEdge : (insert v ({x} : Finset V)).card = 2 := by
    rw [Finset.card_insert_of_notMem hxv, Finset.card_singleton]
  have hNe : (incident (link C v) x).card ≠ 1 := by
    rw [hCount]
    exact hNo _ hEdge
  have hPos : 0 < (incident (link C v) x).card :=
    Finset.card_pos.mpr ⟨t, mem_incident.mpr ⟨ht, hxt⟩⟩
  omega

private theorem incidence_bound {C : Finset (Finset V)} {m n : ℕ}
    (hRank : ∀ t ∈ C, t.card = n)
    (hDegree : ∀ v ∈ support C, m ≤ (incident C v).card) :
    (support C).card * m ≤ C.card * n := by
  refine Finset.card_mul_le_card_mul (fun v (t : Finset V) => v ∈ t)
    (s := support C) (t := C) hDegree ?_
  intro t ht
  have hBelow : (support C).bipartiteBelow (fun v s => v ∈ s) t = t := by
    ext v
    simp only [Finset.mem_bipartiteBelow]
    exact ⟨And.right, fun h => ⟨subset_support ht h, h⟩⟩
  rw [hBelow, hRank t ht]

private theorem link_rank {C : Finset (Finset V)} {v : V}
    (hRank : ∀ t ∈ C, t.card = 3) (e : Finset V) (he : e ∈ link C v) : e.card = 2 := by
  obtain ⟨hve, heC⟩ := mem_link.mp he
  have hCard := hRank _ heC
  rw [Finset.card_insert_of_notMem hve] at hCard
  omega

private theorem link_incidence_bounds {C : Finset (Finset V)} {v : V}
    (hRank : ∀ t ∈ C, t.card = 3) (hNo : NoSingletonEdges C) (hv : v ∈ support C) :
    3 ≤ (support (link C v)).card ∧
      (support (link C v)).card * 2 ≤ (incident C v).card * 2 := by
  obtain ⟨t, ht, hvt⟩ := mem_support.mp hv
  have he : t.erase v ∈ link C v :=
    Finset.mem_image.mpr ⟨t, mem_incident.mpr ⟨ht, hvt⟩, rfl⟩
  have hRankLink := link_rank (v := v) hRank
  have hPos : 0 < (t.erase v).card := by rw [hRankLink _ he]; decide
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hPos
  have hMany : 2 ≤ (link C v).card := (two_le_link_degree hNo (subset_support he hx)).trans
    (Finset.card_le_card (Finset.filter_subset (fun e => x ∈ e) (link C v)))
  obtain ⟨e, heLink, f, hfLink, hef⟩ := Finset.one_lt_card.mp (show 1 < (link C v).card by omega)
  have hLower : 3 ≤ (support (link C v)).card := by
    by_contra hSmall
    have heEq := Finset.eq_of_subset_of_card_le (subset_support heLink)
      (by rw [hRankLink e heLink]; omega)
    have hfEq := Finset.eq_of_subset_of_card_le (subset_support hfLink)
      (by rw [hRankLink f hfLink]; omega)
    exact hef (heEq.trans hfEq.symm)
  refine ⟨hLower, ?_⟩
  rw [← card_link]
  exact incidence_bound hRankLink (fun _ hy => two_le_link_degree hNo hy)

/-- Each vertex in the support of a triangle family with no singleton edge
has at least three incident triangles. -/
theorem three_le_degree {C : Finset (Finset V)} {v : V}
    (hRank : ∀ t ∈ C, t.card = 3) (hNo : NoSingletonEdges C) (hv : v ∈ support C) :
    3 ≤ (incident C v).card := by
  obtain ⟨hLower, hCount⟩ := link_incidence_bounds hRank hNo hv
  omega

private theorem carried_by_four_on_support {C : Finset (Finset V)}
    (hRank : ∀ t ∈ C, t.card = 3) (hNo : NoSingletonEdges C)
    (hSupport : (support C).card ≤ 5) (hPositive : 1 ≤ C.card) (hSmall : C.card ≤ 5) :
    C.card = 4 ∧ ∃ W : Finset V, W.card ≤ 4 ∧ ∀ t ∈ C, t ⊆ W := by
  classical
  let X := support C
  let liftVertex : X ↪ V := Function.Embedding.subtype _
  let liftFace := (Finset.mapEmbedding liftVertex).toEmbedding
  let restrict (t : Finset V) : Finset X := t.subtype (· ∈ X)
  let D := C.image restrict
  have hlift (t : Finset V) (ht : t ∈ C) : liftFace (restrict t) = t := by
    change (t.subtype (· ∈ X)).map (Function.Embedding.subtype _) = t
    apply Finset.subtype_map_of_mem
    exact Finset.subset_biUnion_of_mem id ht
  have hmap : D.map liftFace = C := by
    ext t
    constructor
    · intro ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
      rwa [hlift a ha]
    · intro ht
      exact Finset.mem_map.mpr ⟨restrict t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hlift t ht⟩
  have hDcard : D.card = C.card := by rw [← hmap, Finset.card_map]
  have hDRank : ∀ t ∈ D, t.card = 3 := by
    intro t ht
    have hm : t.map liftVertex ∈ C := by
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨t, ht, rfl⟩
    simpa using hRank (t.map liftVertex) hm
  have hDNo : NoSingletonEdges D := by
    intro e he hOne
    have hfilter : C.filter (e.map liftVertex ⊆ ·) =
        (D.filter (e ⊆ ·)).map liftFace := by
      rw [← hmap, Finset.filter_map]
      congr 1
      ext t
      simp [Function.comp_def, liftFace]
    apply hNo (e.map liftVertex) (by simpa)
    rwa [hfilter, Finset.card_map]
  have hV : Fintype.card X ≤ 5 := by simpa [X] using hSupport
  obtain ⟨hFour, W, hW, hAll⟩ :=
    Q9TriangleSmallSupport.carried_by_four hV D hDRank
      (by omega) (by omega) hDNo
  refine ⟨hDcard.symm.trans hFour, W.map liftVertex, by simpa using hW, ?_⟩
  intro t ht
  rw [← hmap] at ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
  exact Finset.map_subset_map.mpr (hAll s hs)

/-- The cap on four-sets forces at least six triangles in a nonempty
family with no singleton edge. -/
theorem six_le_card {C : Finset (Finset V)}
    (hRank : ∀ t ∈ C, t.card = 3) (hNo : NoSingletonEdges C)
    (hCap : ∀ W : Finset V, W.card ≤ 4 → (C.filter (· ⊆ W)).card ≤ 3)
    (hPositive : 1 ≤ C.card) : 6 ≤ C.card := by
  by_contra h
  have hCount := incidence_bound hRank (fun w hw => three_le_degree hRank hNo hw)
  obtain ⟨hFour, W, hW, hAll⟩ :=
    carried_by_four_on_support hRank hNo (by omega) hPositive (by omega)
  have hCapW := hCap W hW
  have hfilter : C.filter (· ⊆ W) = C := Finset.filter_true_of_mem hAll
  rw [hfilter, hFour] at hCapW
  omega

end Q9TriangleSupportReduction

namespace Q9TetrahedronLinkBound

open Q9TriangleSupportReduction (NoSingletonEdges incident link support)

variable {V : Type*} [DecidableEq V]

/-- No three-set lies in exactly one selected tetrahedron. -/
def NoSingletonTriangles (C : Finset (Finset V)) : Prop :=
  ∀ r : Finset V, r.card = 3 → (C.filter (r ⊆ ·)).card ≠ 1

/-- Reinserting the deleted vertex recovers each incident face, so filtering
the link counts the incident faces whose erasures satisfy the predicate. -/
private theorem card_link_filter (C : Finset (Finset V)) (v : V)
    (p : Finset V → Prop) [DecidablePred p] :
    ((link C v).filter p).card = (C.filter fun t => v ∈ t ∧ p (t.erase v)).card := by
  unfold link incident
  rw [Finset.filter_image, Finset.filter_filter]
  apply Finset.card_image_of_injOn
  apply (Finset.erase_injOn' v).mono
  intro t ht
  exact (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2.1

private theorem noSingletonEdges_link {C : Finset (Finset V)} (v : V)
    (hNo : NoSingletonTriangles C) : NoSingletonEdges (link C v) := by
  intro e he
  rw [card_link_filter C v (e ⊆ ·)]
  by_cases hve : v ∈ e
  · have hEmpty : (C.filter fun t => v ∈ t ∧ e ⊆ t.erase v) = ∅ :=
      Finset.filter_eq_empty_iff.mpr <| fun t _ ht =>
        Finset.notMem_erase v t (ht.2 hve)
    simp [hEmpty]
  · have hFilter : (C.filter fun t => v ∈ t ∧ e ⊆ t.erase v) =
        C.filter (insert v e ⊆ ·) := by
      apply Finset.filter_congr
      intro t _
      rw [Finset.insert_subset_iff, Finset.subset_erase]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hve⟩⟩
    have hTriangle : (insert v e).card = 3 := by
      rw [Finset.card_insert_of_notMem hve, he]
    rw [hFilter]
    exact hNo (insert v e) hTriangle

private theorem link_cap {C : Finset (Finset V)} (v : V)
    (hCap : ∀ W : Finset V, W.card ≤ 5 → (C.filter (· ⊆ W)).card ≤ 3)
    (W : Finset V) (hW : W.card ≤ 4) : ((link C v).filter (· ⊆ W)).card ≤ 3 := by
  rw [card_link_filter C v (· ⊆ W)]
  have hSize : (insert v W).card ≤ 5 :=
    (Finset.card_insert_le v W).trans (Nat.add_le_add_right hW 1)
  refine (Finset.card_le_card ?_).trans (hCap (insert v W) hSize)
  intro t ht
  obtain ⟨htC, _, htW⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨htC, Finset.subset_insert_iff.mpr htW⟩

/-- Each used vertex belongs to at least six selected tetrahedra. -/
theorem six_le_degree {C : Finset (Finset V)} {v : V}
    (hRank : ∀ t ∈ C, t.card = 4) (hNo : NoSingletonTriangles C)
    (hCap : ∀ W : Finset V, W.card ≤ 5 → (C.filter (· ⊆ W)).card ≤ 3)
    (hv : v ∈ support C) : 6 ≤ (incident C v).card := by
  have hRankLink (e : Finset V) (he : e ∈ link C v) : e.card = 3 := by
    unfold link at he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    unfold incident at ht
    obtain ⟨htC, hvt⟩ := Finset.mem_filter.mp ht
    have hCard := Finset.card_erase_add_one hvt
    rw [hRank t htC] at hCard
    omega
  have hCard : (link C v).card = (incident C v).card := by
    simpa only [Finset.filter_true, and_true, incident] using
      card_link_filter C v (fun _ => True)
  have hPositive : 1 ≤ (link C v).card := by
    unfold support at hv
    obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hv
    rw [hCard]
    exact Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hvt⟩⟩
  rw [← hCard]
  exact Q9TriangleSupportReduction.six_le_card hRankLink (noSingletonEdges_link v hNo)
    (link_cap v hCap) hPositive

/-- Counting incidences gives six per used vertex as a lower bound and four
per tetrahedron as an upper bound. -/
theorem support_card_bound {C : Finset (Finset V)}
    (hRank : ∀ t ∈ C, t.card = 4) (hNo : NoSingletonTriangles C)
    (hCap : ∀ W : Finset V, W.card ≤ 5 → (C.filter (· ⊆ W)).card ≤ 3) :
    6 * (support C).card ≤ 4 * C.card := by
  rw [Nat.mul_comm 6, Nat.mul_comm 4]
  refine Finset.card_mul_le_card_mul (fun v (t : Finset V) => v ∈ t)
    (s := support C) (t := C) (fun v hv => six_le_degree hRank hNo hCap hv) ?_
  intro t ht
  change ((support C).filter fun v => v ∈ t).card ≤ 4
  have hSub : t ⊆ support C := Finset.subset_biUnion_of_mem id ht
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSub, hRank t ht]

/-- Eleven selected tetrahedra satisfying the coface condition and cap use
six or seven vertices. -/
theorem support_card_bounds_of_eleven {C : Finset (Finset V)}
    (hRank : ∀ t ∈ C, t.card = 4) (hNo : NoSingletonTriangles C)
    (hCap : ∀ W : Finset V, W.card ≤ 5 → (C.filter (· ⊆ W)).card ≤ 3)
    (hEleven : C.card = 11) :
    6 ≤ (support C).card ∧ (support C).card ≤ 7 := by
  constructor
  · by_cases hSmall : (support C).card ≤ 5
    · have hBound := hCap (support C) hSmall
      have hFilter : C.filter (· ⊆ support C) = C :=
        Finset.filter_true_of_mem fun t ht => Finset.subset_biUnion_of_mem id ht
      rw [hFilter, hEleven] at hBound
      omega
    · omega
  · have hCount := support_card_bound hRank hNo hCap
    omega

end Q9TetrahedronLinkBound
