/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarGrafting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeStarGrafting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual one-contact E grafts have complete old, new and seam edge inventories. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

/-- The star is defined by actual deletion, before choosing any walk. -/
def SupplierStar {m : ℕ} (z v : Configuration m) : Prop :=
  Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v

/-- The full native graph on an independently specified configuration domain. -/
def domainGraph {m : ℕ} (U : Configuration m → Prop) :
    SimpleGraph {v : Configuration m // U v} :=
  (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).induce {v | U v}

def GraftDomain {m : ℕ} (U : Configuration m → Prop) (z v : Configuration m) : Prop :=
  U v ∨ SupplierStar z v

def liftOld {m : ℕ} {U : Configuration m → Prop} (z : Configuration m)
    (v : {v : Configuration m // U v}) :
    {v : Configuration m // GraftDomain U z v} := ⟨v.val, Or.inl v.property⟩

/-- Actual old-cycle edges outside the contact, specified before grafting. -/
def OldUncut {m : ℕ} {U : Configuration m → Prop}
    {base : {v : Configuration m // U v}} (w : (domainGraph U).Walk base base)
    (x y : {v : Configuration m // U v}) (e : Sym2 (Configuration m)) : Prop :=
  e ∈ w.edges.map (Sym2.map Subtype.val) ∧ e ≠ s(x.val, y.val)

/-- The new gaps contribute exactly their uncut native circle edges. -/
def NewUncut {m : ℕ} (z : Configuration m) (e : Sym2 (Configuration m)) : Prop :=
  ∃ i : Fin m, i.val ≠ 0 ∧ NativeCircleEdge (gapAnchor z i) e ∧
    e ≠ s(gapAnchor z i, gapAnchor z i * b m)

/-- The literal E connections, including the final return, are actual c edges. -/
def ESeam {m : ℕ} (z : Configuration m) (e : Sym2 (Configuration m)) : Prop :=
  ∃ i : Fin m, e = s(gapAnchor z i * b m, gapAnchor z i * b m * c m)

private def pieceDomain {m : ℕ} (U : Configuration m → Prop)
    (z : Configuration m) (i : Fin m) (v : Configuration m) : Prop :=
  if i.val = 0 then U v else Circle (gapAnchor z i) v

private theorem gap_in_star {m : ℕ} (hm : 3 ≤ m) (z v : Configuration m)
    (i : Fin m) (hi : Circle (gapAnchor z i) v) : SupplierStar z v :=
  (native_star_circle_partition hm z v).mpr ⟨i, hi⟩

private theorem piece_domains_disjoint {m : ℕ} (hm : 3 ≤ m)
    (U : Configuration m → Prop) (z : Configuration m)
    (hc : ∀ v, U v ∧ SupplierStar z v ↔ Circle z v)
    (i j : Fin m) (hij : i ≠ j) (v : Configuration m) :
    ¬ (pieceDomain U z i v ∧ pieceDomain U z j v) := by
  let zero : Fin m := ⟨0, by omega⟩
  have hz : gapAnchor z zero = z := by simp [gapAnchor, zero]
  by_cases hi : i.val = 0
  · have hie : i = zero := Fin.ext hi
    have hj : j.val ≠ 0 := by
      intro hj
      exact hij (hie.trans (Fin.ext hj).symm)
    simp only [pieceDomain, if_pos hi, if_neg hj]
    rintro ⟨hu, hcircle⟩
    have hzero : Circle (gapAnchor z zero) v :=
      hz ▸ (hc v).mp ⟨hu, gap_in_star hm z v j hcircle⟩
    exact Set.disjoint_left.mp (native_circle_gap_disjoint hm z
      (by intro h; exact hij (hie.trans h))) hzero hcircle
  · by_cases hj : j.val = 0
    · have hje : j = zero := Fin.ext hj
      simp only [pieceDomain, if_neg hi, if_pos hj]
      rintro ⟨hcircle, hu⟩
      have hzero : Circle (gapAnchor z zero) v :=
        hz ▸ (hc v).mp ⟨hu, gap_in_star hm z v i hcircle⟩
      exact Set.disjoint_left.mp (native_circle_gap_disjoint hm z
        (by intro h; exact hij (h.trans hje.symm))) hcircle hzero
    · simp only [pieceDomain, if_neg hi, if_neg hj]
      rintro ⟨hcircle, hcircle'⟩
      exact Set.disjoint_left.mp (native_circle_gap_disjoint hm z hij) hcircle hcircle'

private theorem piece_domains_full {m : ℕ} (hm : 3 ≤ m)
    (U : Configuration m → Prop) (z : Configuration m)
    (hc : ∀ v, U v ∧ SupplierStar z v ↔ Circle z v)
    (v : Configuration m) (hv : GraftDomain U z v) :
    ∃ i : Fin m, pieceDomain U z i v := by
  by_cases hu : U v
  · exact ⟨⟨0, by omega⟩, by simpa [pieceDomain] using hu⟩
  · have hs : SupplierStar z v := hv.resolve_left hu
    obtain ⟨i, hi⟩ := (native_star_circle_partition hm z v).mp hs
    have hiz : i.val ≠ 0 := by
      intro hiz
      have he : gapAnchor z i = z := by simp [gapAnchor, hiz]
      exact hu ((hc v).mpr (he ▸ hi)).1
    exact ⟨i, by simpa [pieceDomain, hiz] using hi⟩

private def retainsNative {m : ℕ} {U : Configuration m → Prop}
    (z : Configuration m) (i : Fin m) (p : Piece (domainGraph (GraftDomain U z))) : Prop :=
  ∀ (x y : {v : Configuration m // GraftDomain U z v}) (g : Configuration m),
    Circle (gapAnchor z i) x.val → (g = a m ∨ g = b m) → y.val = x.val * g →
    s(x.val, y.val) ≠ s(gapAnchor z i, gapAnchor z i * b m) →
    s(x, y) ∈ p.walk.edges

set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_new_piece {m : ℕ} (hm : 3 ≤ m)
    (U : Configuration m → Prop) (z : Configuration m) (i : Fin m) :
    ∃ p : Piece (domainGraph (GraftDomain U z)),
      p.start.val = gapAnchor z i ∧ p.finish.val = gapAnchor z i * b m ∧
        p.walk.IsPath ∧ p.walk.length = 2 * (m + 1) - 1 ∧
          (∀ v, v ∈ p.walk.support ↔ Circle (gapAnchor z i) v.val) ∧
          retainsNative z i p ∧
          (∀ e : Sym2 (Configuration m),
            e ∈ p.walk.edges.map (Sym2.map Subtype.val) ↔
              NativeCircleEdge (gapAnchor z i) e ∧
                e ≠ s(gapAnchor z i, gapAnchor z i * b m)) := by
  obtain ⟨w, hp, hl, _, hs⟩ := native_b_complement hm (gapAnchor z i)
  let w' := w.mapLe (SimpleGraph.deleteEdges_le _)
  have hle : SimpleGraph.mulCayley ({a m, b m} : Set (Configuration m)) ≤
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
    SimpleGraph.mulCayley_mono (by intro x hx; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢; tauto)
  let q := w'.mapLe hle
  have hqp : q.IsPath := (hp.mapLe _).mapLe hle
  have hq : ∀ x ∈ q.support, x ∈ {v | GraftDomain U z v} := by
    intro x hx
    apply Or.inr
    apply gap_in_star hm z x i
    exact (hs x).mp (by simpa only [q, w',
      SimpleGraph.Walk.support_mapLe_eq_support] using hx)
  let r := q.induce {v | GraftDomain U z v} hq
  have hrs : r.support.map Subtype.val = q.support := by
    have he := congrArg SimpleGraph.Walk.support (SimpleGraph.Walk.map_induce q hq)
    rw [SimpleGraph.Walk.support_map] at he
    exact he
  have hre : r.edges.map (Sym2.map Subtype.val) = w'.edges := by
    have heq := congrArg SimpleGraph.Walk.edges (SimpleGraph.Walk.map_induce q hq)
    rw [SimpleGraph.Walk.edges_map] at heq
    change r.edges.map (Sym2.map Subtype.val) = q.edges at heq
    simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using heq
  refine ⟨⟨_, _, r⟩, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    have hmapped : (r.support.map Subtype.val).Nodup := by
      rw [hrs]
      exact hqp.support_nodup
    exact hmapped.of_map
  · have he := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.map_induce q hq)
    simp only [SimpleGraph.Walk.length_map] at he
    change r.length = q.length at he
    exact he.trans (by simpa only [q, w', SimpleGraph.Walk.length_mapLe] using hl)
  · intro v
    change v ∈ r.support ↔ Circle (gapAnchor z i) v.val
    have hmem : v ∈ r.support ↔ v.val ∈ q.support := by
      rw [← hrs]
      constructor
      · intro hv
        exact List.mem_map.mpr ⟨v, hv, rfl⟩
      · intro hv
        obtain ⟨x, hx, hval⟩ := List.mem_map.mp hv
        exact (Subtype.ext hval : x = v) ▸ hx
    rw [hmem]
    simpa only [q, w', SimpleGraph.Walk.support_mapLe_eq_support] using hs v.val
  · intro x y g hx hg hy hne
    have he : s(x.val, y.val) ∈ w'.edges := by
      rw [hy]
      apply (native_complement_edge_inventory hm (gapAnchor z i) (b m) (Or.inr rfl)
        w' (hp.mapLe _) (by simpa only [w', SimpleGraph.Walk.length_mapLe] using hl)
        (by simpa only [w', SimpleGraph.Walk.support_mapLe_eq_support] using hs)
        x.val g hx hg).mpr
      simpa only [hy] using hne
    rw [← hre] at he
    obtain ⟨e, he, heq⟩ := List.mem_map.mp he
    have heq' : Sym2.map Subtype.val e = Sym2.map Subtype.val s(x, y) := heq
    exact (Sym2.map.injective Subtype.val_injective heq' : e = s(x, y)) ▸ he
  · intro e
    change e ∈ r.edges.map (Sym2.map Subtype.val) ↔ _
    rw [hre]
    exact native_complement_full_edge_inventory hm (gapAnchor z i) (b m) (Or.inr rfl)
      w' (hp.mapLe _) (by simpa only [w', SimpleGraph.Walk.length_mapLe] using hl)
      (by simpa only [w', SimpleGraph.Walk.support_mapLe_eq_support] using hs) e

private def oldHom {m : ℕ} (U : Configuration m → Prop) (z : Configuration m) :
    domainGraph U →g domainGraph (GraftDomain U z) where
  toFun := liftOld z
  map_rel' := by intro x y h; exact h

private theorem oldHom_injective {m : ℕ} (U : Configuration m → Prop)
    (z : Configuration m) : Function.Injective (oldHom U z) := by
  intro x y h
  have hv := congrArg (fun v : {v : Configuration m // GraftDomain U z v} => v.val) h
  exact Subtype.ext hv

private def retainsOld {m : ℕ} {U : Configuration m → Prop}
    {base : {v : Configuration m // U v}} (w : (domainGraph U).Walk base base)
    (x y : {v : Configuration m // U v})
    (p : Piece (domainGraph (GraftDomain U x.val))) : Prop :=
  ∀ u v : {v : Configuration m // U v}, s(u, v) ∈ w.edges →
    s(u, v) ≠ s(x, y) → s(liftOld x.val u, liftOld x.val v) ∈ p.walk.edges

private theorem exists_old_piece {m : ℕ} (U : Configuration m → Prop)
    {base : {v : Configuration m // U v}} (w : (domainGraph U).Walk base base)
    (hw : w.IsHamiltonianCycle) (x y : {v : Configuration m // U v})
    (hy : y.val = x.val * b m) (he : s(x, y) ∈ w.edges) :
    ∃ p : Piece (domainGraph (GraftDomain U x.val)),
      p.start.val = x.val ∧ p.finish.val = x.val * b m ∧ p.walk.IsPath ∧
        (∀ v, v ∈ p.walk.support ↔ U v.val) ∧ retainsOld w x y p ∧
          3 ≤ p.walk.support.length ∧
          (∀ e : Sym2 (Configuration m),
            e ∈ p.walk.edges.map (Sym2.map Subtype.val) ↔ OldUncut w x y e) := by
  classical
  let : Fintype {v : Configuration m // U v} := Fintype.ofFinite _
  obtain ⟨q, hq, hqe⟩ := exists_open_cycle_at_edge w hw he
  let r := q.reverse.map (oldHom U x.val)
  refine ⟨⟨_, _, r⟩, rfl, hy, hq.isPath.reverse.map (oldHom_injective U x.val),
    ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [r, SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_reverse,
      List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨u, _, hu⟩
      have hval : u.val = v.val := congrArg Subtype.val hu
      exact hval ▸ u.property
    · intro hv
      exact ⟨⟨v.val, hv⟩, hq.mem_support _, Subtype.ext rfl⟩
  · intro u v hew hne
    have heq := (hqe s(u, v)).mpr ⟨hew, hne⟩
    change s(liftOld x.val u, liftOld x.val v) ∈ r.edges
    simp only [r, SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_reverse,
      List.mem_map, List.mem_reverse]
    exact ⟨s(u, v), heq, rfl⟩
  · have hc := hw.isCycle.three_le_length
    rw [hw.length_eq] at hc
    simpa only [r, SimpleGraph.Walk.support_map, List.length_map,
      SimpleGraph.Walk.support_reverse, List.length_reverse, hq.length_support] using hc
  · intro e
    have hraw : r.edges.map (Sym2.map Subtype.val) =
        (q.edges.map (Sym2.map Subtype.val)).reverse := by
      simp only [r, SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_reverse,
        List.map_reverse, List.map_map, Function.comp_def, Sym2.map_map]
      rfl
    change e ∈ r.edges.map (Sym2.map Subtype.val) ↔ _
    rw [hraw, List.mem_reverse]
    constructor
    · intro he
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      obtain ⟨hdw, hdne⟩ := (hqe d).mp hd
      refine ⟨List.mem_map.mpr ⟨d, hdw, rfl⟩, ?_⟩
      intro h
      exact hdne (Sym2.map.injective Subtype.val_injective h)
    · rintro ⟨hew, hne⟩
      obtain ⟨d, hd, hde⟩ := List.mem_map.mp hew
      refine List.mem_map.mpr ⟨d, (hqe d).mpr ⟨hd, ?_⟩, hde⟩
      intro h
      apply hne
      rw [← hde, h]
      rfl

private theorem exists_graft_piece {m : ℕ} (hm : 3 ≤ m)
    (U : Configuration m → Prop) {base : {v : Configuration m // U v}}
    (w : (domainGraph U).Walk base base) (hw : w.IsHamiltonianCycle)
    (x y : {v : Configuration m // U v}) (hy : y.val = x.val * b m)
    (he : s(x, y) ∈ w.edges) (i : Fin m) :
    ∃ p : Piece (domainGraph (GraftDomain U x.val)),
      p.start.val = gapAnchor x.val i ∧ p.finish.val = gapAnchor x.val i * b m ∧
        p.walk.IsPath ∧ (∀ v, v ∈ p.walk.support ↔ pieceDomain U x.val i v.val) ∧
          (i.val = 0 → retainsOld w x y p) ∧
          (i.val ≠ 0 → retainsNative x.val i p) ∧ 3 ≤ p.walk.support.length ∧
          (∀ e : Sym2 (Configuration m), e ∈ p.walk.edges.map (Sym2.map Subtype.val) ↔
            if i.val = 0 then OldUncut w x y e else
              NativeCircleEdge (gapAnchor x.val i) e ∧
                e ≠ s(gapAnchor x.val i, gapAnchor x.val i * b m)) := by
  by_cases hi : i.val = 0
  · obtain ⟨p, hstart, hfinish, hp, hs, hr, hsize, hinv⟩ := exists_old_piece U w hw x y hy he
    refine ⟨p, ?_, ?_, hp, ?_, fun _ => hr, fun h => (h hi).elim, hsize, ?_⟩
    · simpa only [gapAnchor, hi, pow_zero, mul_one] using hstart
    · simpa only [gapAnchor, hi, pow_zero, mul_one] using hfinish
    · intro v
      simpa only [pieceDomain, if_pos hi] using hs v
    · intro e
      simpa only [if_pos hi] using hinv e
  · obtain ⟨p, hstart, hfinish, hp, hl, hs, hr, hinv⟩ := exists_new_piece hm U x.val i
    refine ⟨p, hstart, hfinish, hp, ?_, fun h => (hi h).elim, fun _ => hr, ?_, ?_⟩
    · intro v
      simpa only [pieceDomain, if_neg hi] using hs v
    · have hs := SimpleGraph.Walk.length_support p.walk
      omega
    · intro e
      simpa only [if_neg hi] using hinv e

private theorem c_ne_one {m : ℕ} (hm : 3 ≤ m) : c m ≠ 1 := by
  intro h
  have he : (c m (0 : Fin (m + 1))).val = m - 2 := by
    rw [c_apply]
    change (if 0 < m - 1 then m - 2 else 0) = m - 2
    exact if_pos (by omega : 0 < m - 1)
  have hz : (c m (0 : Fin (m + 1))).val = 0 := by rw [h]; rfl
  omega

private theorem seam_adj {m : ℕ} (hm : 3 ≤ m) (D : Configuration m → Prop)
    (x y : {v : Configuration m // D v}) (h : x.val * c m = y.val) :
    (domainGraph D).Adj x y := by
  change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj _ _
  rw [SimpleGraph.mulCayley_adj']
  refine ⟨?_, c m, by simp, Or.inl h⟩
  intro hn
  apply c_ne_one hm
  exact mul_left_cancel (h.trans (hn.symm.trans (mul_one _).symm))

private theorem ofFn_endpoints {α : Type*} {n : ℕ} (hn : 0 < n)
    (f : Fin n → α) :
    (List.ofFn f).head? = some (f ⟨0, hn⟩) ∧
      (List.ofFn f).getLast? = some (f ⟨n - 1, by omega⟩) := by
  cases n with
  | zero => omega
  | succ k =>
    constructor
    · rw [List.ofFn_succ]
      rfl
    · rw [List.ofFn_succ_last]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
      rfl

private theorem linked_of_closed_chain {V : Type*} {G : SimpleGraph V}
    (p : Piece G) (ps : List (Piece G))
    (h : (p :: (ps ++ [p])).IsChain (fun x y => G.Adj x.finish y.start)) :
    Linked p ps ∧ G.Adj (finish p ps) p.start := by
  have aux : ∀ (q r : Piece G) (qs : List (Piece G)),
      (q :: (qs ++ [r])).IsChain (fun x y => G.Adj x.finish y.start) →
        Linked q qs ∧ G.Adj (finish q qs) r.start := by
    intro q r qs
    induction qs generalizing q with
    | nil => intro h; exact ⟨trivial, (List.isChain_cons_cons.mp h).1⟩
    | cons s ss ih =>
      intro h
      obtain ⟨hl, hc⟩ := ih s (List.isChain_cons_cons.mp h).2
      exact ⟨⟨(List.isChain_cons_cons.mp h).1, hl⟩, hc⟩
  exact aux p p ps h

private theorem piece_edges_in_chain {V : Type*} {G : SimpleGraph V}
    (p r : Piece G) (ps : List (Piece G)) (hr : r ∈ p :: ps)
    (e : Sym2 V) (he : e ∈ r.walk.edges) : e ∈ chainEdges p ps := by
  induction ps generalizing p with
  | nil =>
    have hre : r = p := List.mem_singleton.mp hr
    subst r
    exact he
  | cons q qs ih =>
    simp only [chainEdges, List.mem_append, List.mem_cons]
    rcases List.mem_cons.mp hr with hre | hr
    · subst r
      exact Or.inl he
    · exact Or.inr (Or.inr (ih q hr))

private theorem seam_edge_at {V : Type*} {G : SimpleGraph V}
    (p : Piece G) (ps : List (Piece G)) (i : ℕ) (hi : i + 1 < (p :: ps).length) :
    s(((p :: ps)[i]'(by omega)).finish, ((p :: ps)[i + 1]'hi).start) ∈
      chainEdges p ps := by
  induction ps generalizing p i with
  | nil => simp only [List.length_cons, List.length_nil] at hi; omega
  | cons q qs ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.zero_add, List.getElem_cons_succ,
        chainEdges, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inl trivial)
    | succ i =>
      have hi' : i + 1 < (q :: qs).length := by
        simp only [List.length_cons] at hi ⊢
        omega
      have he := ih q i hi'
      simpa only [chainEdges, List.getElem_cons_succ, Nat.succ_eq_add_one] using
        List.mem_append_right p.walk.edges (List.mem_cons_of_mem _ he)

private theorem finish_of_getLast {V : Type*} {G : SimpleGraph V}
    (p r : Piece G) (ps : List (Piece G)) (h : (p :: ps).getLast? = some r) :
    finish p ps = r.finish := by
  induction ps generalizing p with
  | nil =>
    have hpr : p = r := by simpa only [List.getLast?_singleton, Option.some.injEq] using h
    exact congrArg Piece.finish hpr
  | cons q qs ih =>
    apply ih q
    simpa only [List.getLast?_cons_cons] using h

/-- If an independent old domain meets a new supplier star in exactly one
complete circle, its actual contact b-edge can be replaced by the complete E
ring. The resulting actual Hamilton cycle retains every other old edge and
every uncut native a/b edge in the new gap circles. Its complete edge set is
exactly those old edges, the new uncut edges and the literal E c seams. -/
theorem native_one_contact_graft {m : ℕ} (hm : 3 ≤ m)
    (U : Configuration m → Prop) {base : {v : Configuration m // U v}}
    (w : (domainGraph U).Walk base base) (hw : w.IsHamiltonianCycle)
    (x y : {v : Configuration m // U v}) (hy : y.val = x.val * b m)
    (he : s(x, y) ∈ w.edges)
    (hc : ∀ v, U v ∧ SupplierStar x.val v ↔ Circle x.val v) :
    ∃ start : {v : Configuration m // GraftDomain U x.val v}, start.val = x.val ∧
      ∃ q : (domainGraph (GraftDomain U x.val)).Walk start start,
        q.IsHamiltonianCycle ∧
          (∀ u v : {v : Configuration m // U v}, s(u, v) ∈ w.edges →
            s(u, v) ≠ s(x, y) → s(liftOld x.val u, liftOld x.val v) ∈ q.edges) ∧
          (∀ (i : Fin m), i.val ≠ 0 →
            ∀ (u v : {v : Configuration m // GraftDomain U x.val v}) (g : Configuration m),
              Circle (gapAnchor x.val i) u.val → (g = a m ∨ g = b m) →
              v.val = u.val * g →
              s(u.val, v.val) ≠ s(gapAnchor x.val i, gapAnchor x.val i * b m) →
              s(u, v) ∈ q.edges) ∧
          (∀ i : Fin m,
            ∃ u v : {v : Configuration m // GraftDomain U x.val v},
              u.val = gapAnchor x.val i * b m ∧ v.val = u.val * c m ∧
                s(u, v) ∈ q.edges) ∧
          ∀ e : Sym2 (Configuration m),
            e ∈ q.edges.map (Sym2.map Subtype.val) ↔
              OldUncut w x y e ∨ NewUncut x.val e ∨ ESeam x.val e := by
  classical
  let : BEq {v : Configuration m // GraftDomain U x.val v} := instBEqOfDecidableEq
  let f : Fin m → Piece (domainGraph (GraftDomain U x.val)) :=
    fun i => Classical.choose (exists_graft_piece hm U w hw x y hy he i)
  have hf (i : Fin m) : (f i).start.val = gapAnchor x.val i ∧
      (f i).finish.val = gapAnchor x.val i * b m ∧ (f i).walk.IsPath ∧
      (∀ v, v ∈ (f i).walk.support ↔ pieceDomain U x.val i v.val) ∧
      (i.val = 0 → retainsOld w x y (f i)) ∧
      (i.val ≠ 0 → retainsNative x.val i (f i)) ∧ 3 ≤ (f i).walk.support.length ∧
      (∀ e : Sym2 (Configuration m), e ∈ (f i).walk.edges.map (Sym2.map Subtype.val) ↔
        if i.val = 0 then OldUncut w x y e else
          NativeCircleEdge (gapAnchor x.val i) e ∧
            e ≠ s(gapAnchor x.val i, gapAnchor x.val i * b m)) :=
    Classical.choose_spec (exists_graft_piece hm U w hw x y hy he i)
  let zero : Fin m := ⟨0, by omega⟩
  have hbc : (b m * c m) ^ m = 1 := by
    have h := (native_e_simple_trace hm x.val).1
    simpa only [eWord, List.prod_flatten, List.map_replicate,
      List.prod_replicate, List.prod_cons, List.prod_nil, mul_one] using h
  have hchain : (List.ofFn f).IsChain
      (fun p q => p.finish.val * c m = q.start.val) := by
    apply List.isChain_ofFn.mpr
    intro j hj
    rw [(hf ⟨j, by omega⟩).2.1, (hf ⟨j + 1, hj⟩).1]
    simp only [gapAnchor, pow_succ, mul_assoc]
  have hclosed : (List.ofFn f ++ [f zero]).IsChain
      (fun p q => p.finish.val * c m = q.start.val) := by
    apply hchain.append (List.IsChain.singleton _)
    rw [(ofFn_endpoints (by omega : 0 < m) f).2]
    simp only [List.head?_singleton, Option.mem_some_iff]
    intro p hp q hq
    subst p; subst q
    rw [(hf ⟨m - 1, by omega⟩).2.1, (hf zero).1]
    simp only [gapAnchor, zero, pow_zero, mul_one]
    simp only [mul_assoc]
    rw [← pow_succ, show m - 1 + 1 = m by omega, hbc, mul_one]
  have hnodup : ((List.ofFn f).flatMap (fun p => p.walk.support)).Nodup := by
    rw [List.ofFn_eq_map, List.flatMap_map]
    apply List.nodup_flatMap.mpr
    constructor
    · intro i _
      exact (hf i).2.2.1.support_nodup
    · apply (List.nodup_finRange m).imp
      intro i j hij
      change List.Disjoint (f i).walk.support (f j).walk.support
      rw [List.disjoint_left]
      intro v hi hj
      exact piece_domains_disjoint hm U x.val hc i j hij v.val
        ⟨((hf i).2.2.2.1 v).mp hi, ((hf j).2.2.2.1 v).mp hj⟩
  cases hlist : List.ofFn f with
  | nil =>
    have hlen : (List.ofFn f).length = m := List.length_ofFn
    rw [hlist] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons p ps =>
    have hpzero : p = f zero := by
      have hhead := (ofFn_endpoints (by omega : 0 < m) f).1
      rw [hlist] at hhead
      simpa only [List.head?_cons, Option.some.injEq] using hhead
    have hlinked : Linked p ps ∧ (domainGraph (GraftDomain U x.val)).Adj
        (finish p ps) p.start := by
      apply linked_of_closed_chain
      have hh := hclosed.imp (fun _ _ h => seam_adj hm _ _ _ h)
      simpa only [hlist, hpzero, List.cons_append] using hh
    have hfull : ∀ v : {v : Configuration m // GraftDomain U x.val v},
        ((p :: ps).flatMap (fun p => p.walk.support)).count v = 1 := by
      intro v
      apply List.count_eq_one_of_mem
      · simpa only [hlist] using hnodup
      · obtain ⟨i, hi⟩ := piece_domains_full hm U x.val hc v.val v.property
        have hv : v ∈ (List.ofFn f).flatMap (fun p => p.walk.support) :=
          List.mem_flatMap.mpr
          ⟨f i, List.mem_ofFn.mpr ⟨i, rfl⟩, ((hf i).2.2.2.1 v).mpr hi⟩
        simpa only [hlist] using hv
    have hsize : 3 ≤ ((p :: ps).flatMap (fun p => p.walk.support)).length := by
      have hs := (hf zero).2.2.2.2.2.2.1
      rw [← hpzero] at hs
      simp only [List.flatMap_cons, List.length_append]
      omega
    obtain ⟨q, hq, _, hqe⟩ :=
      exists_spliced_hamiltonian_cycle p ps hlinked.1 hlinked.2 hfull hsize
    have hstart : p.start.val = x.val := by
      rw [hpzero, (hf zero).1]
      simp only [gapAnchor, zero, pow_zero, mul_one]
    have hseams : ∀ i : Fin m,
        ∃ u v : {v : Configuration m // GraftDomain U x.val v},
          u.val = gapAnchor x.val i * b m ∧ v.val = u.val * c m ∧
            s(u, v) ∈ q.edges := by
      intro i
      by_cases hi : i.val + 1 < m
      · let next : Fin m := ⟨i.val + 1, hi⟩
        have he : s((f i).finish, (f next).start) ∈ chainEdges p ps := by
          have hil : i.val + 1 < (p :: ps).length := by
            rw [← hlist, List.length_ofFn]
            exact hi
          have he := seam_edge_at p ps i.val hil
          have hgeti : (p :: ps)[i.val]'(by omega) = f i := by
            simp only [← hlist, List.getElem_ofFn]
          have hgetnext : (p :: ps)[i.val + 1]'hil = f next := by
            simp only [← hlist, List.getElem_ofFn, next]
          rwa [hgeti, hgetnext] at he
        refine ⟨(f i).finish, (f next).start, (hf i).2.1, ?_, ?_⟩
        · rw [(hf i).2.1, (hf next).1]
          simp only [gapAnchor, next, pow_succ, mul_assoc]
        · rw [hqe]
          exact List.mem_cons_of_mem _ (List.mem_reverse.mpr he)
      · have hilast : i = ⟨m - 1, by omega⟩ :=
          Fin.ext (by change i.val = m - 1; have hlt := i.isLt; omega)
        have hlast : (p :: ps).getLast? = some (f i) := by
          rw [← hlist]
          simpa only [hilast] using (ofFn_endpoints (by omega : 0 < m) f).2
        have hfinish := finish_of_getLast p (f i) ps hlast
        have hc : (f i).finish.val * c m = p.start.val := by
          rw [(hf i).2.1, hstart, hilast]
          simp only [gapAnchor, mul_assoc]
          rw [← pow_succ, show m - 1 + 1 = m by omega, hbc, mul_one]
        refine ⟨(f i).finish, p.start, (hf i).2.1, hc.symm, ?_⟩
        rw [hqe, hfinish]
        exact List.mem_cons.mpr (Or.inl Sym2.eq_swap)
    have hpiece_in_q (i : Fin m) (e : Sym2 (Configuration m))
        (he : e ∈ (f i).walk.edges.map (Sym2.map Subtype.val)) :
        e ∈ q.edges.map (Sym2.map Subtype.val) := by
      obtain ⟨d, hd, hde⟩ := List.mem_map.mp he
      refine List.mem_map.mpr ⟨d, ?_, hde⟩
      rw [hqe]
      apply List.mem_cons_of_mem
      apply List.mem_reverse.mpr
      apply piece_edges_in_chain p (f i) ps
      · rw [← hlist]
        exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · exact hd
    have hclass (d : Sym2 {v : Configuration m // GraftDomain U x.val v})
        (hd : d ∈ chainEdges p ps) :
        OldUncut w x y (Sym2.map Subtype.val d) ∨
          NewUncut x.val (Sym2.map Subtype.val d) ∨
            ESeam x.val (Sym2.map Subtype.val d) := by
      rcases chain_edge_cases p ps d hd with ⟨r, hr, he⟩ | ⟨i, hi, he⟩
      · rw [← hlist] at hr
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
        have hinv := ((hf i).2.2.2.2.2.2.2 (Sym2.map Subtype.val d)).mp
          (List.mem_map.mpr ⟨d, he, rfl⟩)
        by_cases hi : i.val = 0
        · exact Or.inl (by simpa only [if_pos hi] using hinv)
        · exact Or.inr (Or.inl ⟨i, hi, by simpa only [if_neg hi] using hinv⟩)
      · have him : i + 1 < m := by
          simpa only [← hlist, List.length_ofFn] using hi
        let curr : Fin m := ⟨i, by omega⟩
        let next : Fin m := ⟨i + 1, him⟩
        have hgetcurr : (p :: ps)[i]'(by omega) = f curr := by
          simp only [← hlist, List.getElem_ofFn, curr]
        have hgetnext : (p :: ps)[i + 1]'hi = f next := by
          simp only [← hlist, List.getElem_ofFn, next]
        refine Or.inr (Or.inr ⟨curr, ?_⟩)
        rw [he, hgetcurr, hgetnext, Sym2.map_mk, (hf curr).2.1, (hf next).1]
        simp only [gapAnchor, curr, next, pow_succ, mul_assoc]
    have hclosing : ESeam x.val (Sym2.map Subtype.val s(p.start, finish p ps)) := by
      let last : Fin m := ⟨m - 1, by omega⟩
      have hlast : (p :: ps).getLast? = some (f last) := by
        rw [← hlist]
        exact (ofFn_endpoints (by omega : 0 < m) f).2
      have hfinish := finish_of_getLast p (f last) ps hlast
      have hreturn : gapAnchor x.val last * b m * c m = x.val := by
        simp only [gapAnchor, last, mul_assoc]
        rw [← pow_succ, show m - 1 + 1 = m by omega, hbc, mul_one]
      refine ⟨last, ?_⟩
      rw [Sym2.map_mk, hstart, hfinish, (hf last).2.1, hreturn]
      exact Sym2.eq_swap
    refine ⟨p.start, hstart, q, hq, ?_, ?_, hseams, ?_⟩
    · intro u v hew hne
      have hr := (hf zero).2.2.2.2.1 rfl u v hew hne
      rw [hqe]
      apply List.mem_cons_of_mem
      apply List.mem_reverse.mpr
      apply piece_edges_in_chain p (f zero) ps
      · rw [← hpzero]
        exact List.mem_cons_self
      · exact hr
    · intro i hi u v g hu hg hv hne
      have hr := (hf i).2.2.2.2.2.1 hi u v g hu hg hv hne
      rw [hqe]
      apply List.mem_cons_of_mem
      apply List.mem_reverse.mpr
      apply piece_edges_in_chain p (f i) ps
      · rw [← hlist]
        exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · exact hr
    · intro e
      constructor
      · intro he
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        rw [hqe, List.mem_cons, List.mem_reverse] at hd
        rcases hd with hd | hd
        · subst d
          exact Or.inr (Or.inr hclosing)
        · exact hclass d hd
      · rintro (he | he | he)
        · apply hpiece_in_q zero e
          apply ((hf zero).2.2.2.2.2.2.2 e).mpr
          simpa only [zero, Fin.val_mk, if_true] using he
        · obtain ⟨i, hi, hn, hne⟩ := he
          apply hpiece_in_q i e
          apply ((hf i).2.2.2.2.2.2.2 e).mpr
          simpa only [if_neg hi] using And.intro hn hne
        · obtain ⟨i, rfl⟩ := he
          obtain ⟨u, v, hu, hv, he⟩ := hseams i
          refine List.mem_map.mpr ⟨s(u, v), he, ?_⟩
          simp only [Sym2.map_mk, hv, hu]

#print axioms native_one_contact_graft

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
