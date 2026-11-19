module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Lower bound for a nonempty family of top triples on seven coordinates. -/

open Finset SimpleGraph
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private lemma two_triples_in_four {α : Type*} [DecidableEq α]
    (T : Finset (Finset α)) (s t : Finset α) (ht : t ∈ T) (hts : t ⊆ s)
    (hEven : Even (T.filter (· ⊆ s)).card) (hMax : (T.filter (· ⊆ s)).card ≤ 2) :
    ∃ v ∈ T, v ⊆ s ∧ v ≠ t ∧
      ∀ w ∈ T, w ⊆ s → w = t ∨ w = v := by
  let A := T.filter (· ⊆ s)
  have htA : t ∈ A := mem_filter.mpr ⟨ht, hts⟩
  have hpos := card_pos.mpr ⟨t, htA⟩
  obtain ⟨n, hn⟩ := hEven
  have hA : A.card = 2 := by dsimp [A] at hpos ⊢; omega
  obtain ⟨a, b, hab, hrep⟩ := card_eq_two.mp hA
  have helper {x y : Finset α} (hxy : x ≠ y) (h : A = {x, y})
      (hx : t = x) : ∃ v ∈ T, v ⊆ s ∧ v ≠ t ∧
        ∀ w ∈ T, w ⊆ s → w = t ∨ w = v := by
    have hy : y ∈ A := by rw [h]; simp
    obtain ⟨hyT, hys⟩ := mem_filter.mp hy
    refine ⟨y, hyT, hys, ?_, ?_⟩
    · exact hx ▸ hxy.symm
    · intro w hw hws
      have hwA : w ∈ A := mem_filter.mpr ⟨hw, hws⟩
      rw [h] at hwA
      simpa [hx] using hwA
  have ht' : t = a ∨ t = b := by simpa [hrep] using htA
  rcases ht' with ha | hb
  · exact helper hab hrep ha
  · exact helper hab.symm (by rw [hrep, pair_comm]) hb

/-- A nonempty triple family on seven coordinates with zero or two triples in
each four-set and at most three triples through each pair has at least nine
members. -/
public theorem nine_le_top_triple_family {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = 7) (T : Finset (Finset α))
    (hthree : ∀ t ∈ T, t.card = 3) (hT : T.Nonempty)
    (hfour : ∀ s : Finset α, s.card = 4 →
      Even (T.filter (· ⊆ s)).card ∧ (T.filter (· ⊆ s)).card ≤ 2)
    (hpair : ∀ p : Finset α, p.card = 2 → (T.filter (p ⊆ ·)).card ≤ 3) :
    9 ≤ T.card := by
  classical
  obtain ⟨t, ht⟩ := hT
  let O := (univ : Finset α) \ t
  have hO : O.card = 4 := by
    rw [show O = univ \ t by rfl, card_sdiff_of_subset (subset_univ _),
      card_univ, hα, hthree t ht]
  let V := (O : Set α)
  have hV : Fintype.card V = 4 := by simpa [V] using hO
  have hout (a : V) : a.val ∉ t := (mem_sdiff.mp a.property).2
  have hchoose (a : V) : ∃ v ∈ T, v ⊆ insert a.val t ∧ v ≠ t ∧
      ∀ w ∈ T, w ⊆ insert a.val t → w = t ∨ w = v := by
    have hsize : (insert a.val t).card = 4 := by
      rw [card_insert_of_notMem (hout a), hthree t ht]
    have h := hfour _ hsize
    exact two_triples_in_four T _ t ht (subset_insert _ _) h.1 h.2
  choose neighbor hnT hnsub hnneq hnunique using hchoose
  have hcontains (a : V) : a.val ∈ neighbor a := by
    by_contra ha
    apply hnneq a
    apply eq_of_subset_of_card_le
    · intro x hx
      rcases mem_insert.mp (hnsub a hx) with h | h
      · exact False.elim (ha (h ▸ hx))
      · exact h
    · rw [hthree t ht, hthree _ (hnT a)]
  let pair (a : V) := (neighbor a).erase a.val
  have hpairT (a : V) : pair a ⊆ t := by
    intro x hx
    have h := mem_erase.mp hx
    exact (mem_insert.mp (hnsub a h.2)).resolve_left h.1
  have hpairSize (a : V) : (pair a).card = 2 := by
    rw [show pair a = (neighbor a).erase a.val by rfl,
      card_erase_of_mem (hcontains a), hthree _ (hnT a)]
  have hneighbor (a : V) : insert a.val (pair a) = neighbor a :=
    insert_erase (hcontains a)
  have hdifference (a : V) : neighbor a \ t = {a.val} := by
    rw [← hneighbor]
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hxt⟩ := mem_sdiff.mp hx
      exact mem_singleton.mpr ((mem_insert.mp hx).resolve_right fun hh => hxt (hpairT a hh))
    · intro hx
      simp only [mem_singleton] at hx
      subst x
      exact mem_sdiff.mpr ⟨mem_insert_self _ _, hout a⟩
  have hneighInj : Function.Injective neighbor := by
    intro a b hab
    have h := congrArg (fun s : Finset α => s \ t) hab
    rw [hdifference, hdifference] at h
    exact Subtype.ext (singleton_injective h)
  have hfiber (a : V) : (univ.filter (fun b : V => pair b = pair a)).card ≤ 2 := by
    let fiber := univ.filter (fun b : V => pair b = pair a)
    have hsub : insert t (fiber.image neighbor) ⊆ T.filter (pair a ⊆ ·) := by
      intro s hs
      rcases mem_insert.mp hs with rfl | hs
      · exact mem_filter.mpr ⟨ht, hpairT a⟩
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hs
        have h := (mem_filter.mp hb).2
        exact mem_filter.mpr ⟨hnT b, h ▸ erase_subset _ _⟩
    have hn : t ∉ fiber.image neighbor := by
      intro ht'
      obtain ⟨b, _, he⟩ := mem_image.mp ht'
      exact hnneq b he
    have h := (card_le_card hsub).trans (hpair _ (hpairSize a))
    rw [card_insert_of_notMem hn, card_image_of_injective _ hneighInj] at h
    change fiber.card ≤ 2
    omega
  let G : SimpleGraph V :=
    { Adj := fun a b => pair a ≠ pair b
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  have hdeg (a : V) : 2 ≤ G.degree a := by
    have he : G.neighborFinset a = univ.filter (fun b : V => pair b ≠ pair a) := by
      ext b
      simp [G, ne_comm]
    have hs := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun b => pair b = pair a)
    have hsame : (univ.filter (fun b : V => ¬ pair b = pair a)) =
        univ.filter (fun b : V => pair b ≠ pair a) := by
      ext b
      simp
    rw [hsame, card_univ, hV] at hs
    have hf := hfiber a
    rw [← G.card_neighborFinset_eq_degree, he]
    omega
  have hEdges : 4 ≤ G.edgeFinset.card := by
    have hs := G.sum_degrees_eq_twice_card_edges
    have hsum := sum_le_sum (s := (univ : Finset V)) (fun a _ => hdeg a)
    rw [sum_const, card_univ, hV, hs] at hsum
    change 8 ≤ 2 * G.edgeFinset.card at hsum
    omega
  have otherTriple (a b : V) (hab : pair a ≠ pair b) :
      ∃ u ∈ T, u \ t = {a.val, b.val} := by
    have hvne : a.val ≠ b.val := fun e => hab (congrArg pair (Subtype.ext e))
    let s := insert a.val (insert b.val (pair a))
    have han : a.val ∉ pair a := fun h => hout a (hpairT a h)
    have hbn : b.val ∉ pair a := fun h => hout b (hpairT a h)
    have hsa : a.val ∉ insert b.val (pair a) := by simp [hvne, han]
    have hs : s.card = 4 := by
      rw [show s = insert a.val (insert b.val (pair a)) by rfl,
        card_insert_of_notMem hsa, card_insert_of_notMem hbn, hpairSize a]
    have hsubA : neighbor a ⊆ s := by
      rw [← hneighbor a]
      intro x hx
      rcases mem_insert.mp hx with he | hx
      · exact mem_insert.mpr (Or.inl he)
      · exact mem_insert_of_mem (mem_insert_of_mem hx)
    have hsub_pair {u : Finset α} (hut : u ⊆ t) (hus : u ⊆ s) : u ⊆ pair a := by
      intro x hx
      rcases mem_insert.mp (hus hx) with ha | hs'
      · exact False.elim (hout a (ha ▸ hut hx))
      · rcases mem_insert.mp hs' with hb | hh
        · exact False.elim (hout b (hb ▸ hut hx))
        · exact hh
    have ht_not : ¬ t ⊆ s := by
      intro ht'
      have hc := card_le_card (hsub_pair (Subset.rfl) ht')
      rw [hthree t ht, hpairSize a] at hc
      omega
    have hb_not : ¬ neighbor b ⊆ s := by
      intro hb'
      apply hab
      symm
      exact eq_of_subset_of_card_le (hsub_pair (hpairT b) ((erase_subset _ _).trans hb'))
        (by rw [hpairSize a, hpairSize b])
    have hh := hfour s hs
    obtain ⟨u, huT, hu, hu_ne, _⟩ :=
      two_triples_in_four T s (neighbor a) (hnT a) hsubA hh.1 hh.2
    have huA : a.val ∈ u := by
      by_contra hna
      have hus : u ⊆ insert b.val t := by
        intro x hx
        exact (mem_insert.mp (hu hx)).elim
          (fun e => False.elim (hna (e ▸ hx))) fun h =>
            (mem_insert.mp h).elim (fun e => mem_insert.mpr (Or.inl e))
              (fun h' => mem_insert_of_mem (hpairT a h'))
      rcases hnunique b u huT hus with he | he
      · exact ht_not (he ▸ hu)
      · exact hb_not (he ▸ hu)
    have huB : b.val ∈ u := by
      by_contra hnb
      have hus : u ⊆ insert a.val t := by
        intro x hx
        rcases mem_insert.mp (hu hx) with ha | hs'
        · exact mem_insert.mpr (Or.inl ha)
        · rcases mem_insert.mp hs' with hb | hp
          · exact False.elim (hnb (hb ▸ hx))
          · exact mem_insert_of_mem (hpairT a hp)
      rcases hnunique a u huT hus with he | he
      · exact ht_not (he ▸ hu)
      · exact hu_ne he
    refine ⟨u, huT, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨hxU, hxt⟩ := mem_sdiff.mp hx
      rcases mem_insert.mp (hu hxU) with ha | hs'
      · exact mem_insert.mpr (Or.inl ha)
      · rcases mem_insert.mp hs' with hb | hp
        · exact mem_insert.mpr (Or.inr (mem_singleton.mpr hb))
        · exact False.elim (hxt (hpairT a hp))
    · intro hx
      rcases mem_insert.mp hx with ha | hb
      · subst x
        exact mem_sdiff.mpr ⟨huA, hout a⟩
      · rw [mem_singleton] at hb
        subst x
        exact mem_sdiff.mpr ⟨huB, hout b⟩
  let U := T.filter (fun u => (u \ t).card = 2)
  let asFinset (e : Sym2 V) : Finset α := e.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : Function.Injective asFinset := by
    intro e f h
    apply Sym2.ext
    intro a
    have hmem (z : Sym2 V) : a.val ∈ asFinset z ↔ a ∈ z := by
      simp [asFinset]
    rw [← hmem, ← hmem, h]
  have hEdgeImage : G.edgeFinset.image asFinset ⊆ U.image (fun u => u \ t) := by
    intro z hz
    obtain ⟨e, he, hez⟩ := mem_image.mp hz
    subst z
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : pair a ≠ pair b := by
        exact (SimpleGraph.mem_edgeSet G).mp (G.mem_edgeFinset.mp he)
      obtain ⟨u, hu, hrs⟩ := otherTriple a b hab
      have hneq : a.val ≠ b.val := fun e => hab (congrArg pair (Subtype.ext e))
      have huU : u ∈ U := by
        apply mem_filter.mpr
        refine ⟨hu, ?_⟩
        simp [hrs, hneq]
      apply mem_image.mpr
      refine ⟨u, huU, ?_⟩
      simp [hrs, asFinset, Sym2.toFinset_mk_eq]
  have hU : 4 ≤ U.card := by
    have h := card_le_card hEdgeImage
    rw [card_image_of_injective _ hmap] at h
    exact hEdges.trans (h.trans (card_image_le))
  let N : Finset (Finset α) := univ.image neighbor
  have hN : N.card = 4 := by
    rw [show N = univ.image neighbor by rfl, card_image_of_injective _ hneighInj, card_univ, hV]
  have htN : t ∉ N := by
    intro h
    obtain ⟨a, _, ha⟩ := mem_image.mp h
    exact hnneq a ha
  have hNU : Disjoint (insert t N) U := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hc := (mem_filter.mp hv).2
    rcases mem_insert.mp hu with rfl | hu'
    · simp at hc
    · obtain ⟨a, _, rfl⟩ := mem_image.mp hu'
      simp [hdifference] at hc
  have hAll : (insert t N ∪ U) ⊆ T := by
    intro u hu
    rcases mem_union.mp hu with hu' | hu'
    · rcases mem_insert.mp hu' with rfl | hu''
      · exact ht
      · obtain ⟨a, _, rfl⟩ := mem_image.mp hu''
        exact hnT a
    · exact (mem_filter.mp hu').1
  have h := card_le_card hAll
  rw [card_union_of_disjoint hNU, card_insert_of_notMem htN, hN] at h
  omega

#print axioms nine_le_top_triple_family

end D5.S3.Combinatorics.Graph.HypercubeCritical
