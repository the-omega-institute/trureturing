/- GID: D5/S3/Combinatorics/Graph/DeltaY/MoveModel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DeltaY/MoveModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Triangle-star moves on simple graphs, finite labels, transport, and strong edge count. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Option

/-!
A forward move inserts a new center and deletes the three edges of a triangle.
A reverse move deletes a center of degree three and inserts all three neighbor pairs
by simple-edge union. Strong reverse moves require an independent neighbor triple.
Finite active labels give a computable model, with lifts and realizations on arbitrary
finite simple graphs.
-/

set_option autoImplicit false
set_option warningAsError true

namespace DeltaY

open Finset Relation

universe u v

structure State where
  active : Finset ℕ
  edges : Finset (Sym2 ℕ)

def State.Adj (G : State) (x y : ℕ) : Prop := s(x, y) ∈ G.edges

instance (G : State) : DecidableRel G.Adj := fun x y =>
  inferInstanceAs (Decidable (s(x, y) ∈ G.edges))

def State.Valid (G : State) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → x ∈ G.active ∧ y ∈ G.active ∧ x ≠ y

theorem State.adj_symm {G : State} {x y : ℕ} (h : G.Adj x y) : G.Adj y x := by
  simpa only [State.Adj, Sym2.eq_swap] using h

def State.neighbors (G : State) (x : ℕ) : Finset ℕ := G.active.filter (G.Adj x)

theorem State.mem_neighbors {G : State} (hG : G.Valid) {x y : ℕ} :
    y ∈ G.neighbors x ↔ G.Adj x y := by
  simp only [State.neighbors, mem_filter]
  exact ⟨And.right, fun h => ⟨(hG h).2.1, h⟩⟩

def State.degree (G : State) (x : ℕ) : ℕ := (G.neighbors x).card

def State.MinDegree (G : State) (d : ℕ) : Prop := ∀ x ∈ G.active, d ≤ G.degree x

structure Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c

def Triple.verts (T : Triple) : Finset ℕ := {T.a, T.b, T.c}

theorem Triple.mem_verts (T : Triple) (x : ℕ) :
    x ∈ T.verts ↔ x = T.a ∨ x = T.b ∨ x = T.c := by
  simp [Triple.verts]

theorem Triple.card_verts (T : Triple) : T.verts.card = 3 :=
  Finset.card_triple_eq_three_iff.mpr ⟨T.ab, T.ac, T.bc⟩

def Triple.pairs (T : Triple) : Finset (Sym2 ℕ) :=
  {s(T.a, T.b), s(T.a, T.c), s(T.b, T.c)}

def Triple.spokes (T : Triple) (o : ℕ) : Finset (Sym2 ℕ) :=
  {s(o, T.a), s(o, T.b), s(o, T.c)}

theorem Triple.mem_pairs (T : Triple) (x y : ℕ) :
    s(x, y) ∈ T.pairs ↔ x ∈ T.verts ∧ y ∈ T.verts ∧ x ≠ y := by
  have := T.ab; have := T.ac; have := T.bc
  simp only [Triple.pairs, mem_insert, mem_singleton, Sym2.eq_iff, Triple.mem_verts]
  grind

private theorem Triple.mem_spokes (T : Triple) (o x y : ℕ) :
    s(x, y) ∈ T.spokes o ↔ (x = o ∧ y ∈ T.verts) ∨ (y = o ∧ x ∈ T.verts) := by
  simp only [Triple.spokes, mem_insert, mem_singleton, Sym2.eq_iff, Triple.mem_verts]
  grind

private theorem Triple.card_pairs (T : Triple) : T.pairs.card = 3 := by
  unfold Triple.pairs
  apply Finset.card_triple_eq_three_iff.mpr
  have hab := T.ab
  have hac := T.ac
  have hbc := T.bc
  simp only [ne_eq, Sym2.eq_iff]
  grind

private theorem Triple.card_spokes (T : Triple) (o : ℕ) : (T.spokes o).card = 3 := by
  unfold Triple.spokes
  apply Finset.card_triple_eq_three_iff.mpr
  have hab := T.ab
  have hac := T.ac
  have hbc := T.bc
  simp only [ne_eq, Sym2.eq_iff]
  grind

def State.forward (G : State) (T : Triple) (o : ℕ) : State :=
  ⟨insert o G.active, (G.edges \ T.pairs) ∪ T.spokes o⟩

def State.reverse (G : State) (T : Triple) (o : ℕ) : State :=
  ⟨G.active.erase o, (G.edges \ T.spokes o) ∪ T.pairs⟩

def ForwardOK (G : State) (T : Triple) (o : ℕ) : Prop :=
  T.verts ⊆ G.active ∧ o ∉ G.active ∧ T.pairs ⊆ G.edges

def ReverseOK (G : State) (T : Triple) (o : ℕ) : Prop :=
  o ∈ G.active ∧ G.neighbors o = T.verts

def Independent (G : State) (T : Triple) : Prop := Disjoint G.edges T.pairs

theorem forward_adj {G : State} {T : Triple} {o x y : ℕ} :
    (G.forward T o).Adj x y ↔
      (G.Adj x y ∧ ¬ (x ∈ T.verts ∧ y ∈ T.verts ∧ x ≠ y)) ∨
      (x = o ∧ y ∈ T.verts) ∨ (y = o ∧ x ∈ T.verts) := by
  simp only [State.forward, State.Adj, mem_union, mem_sdiff,
    Triple.mem_pairs, Triple.mem_spokes]

theorem reverse_adj {G : State} {T : Triple} {o x y : ℕ} :
    (G.reverse T o).Adj x y ↔
      (G.Adj x y ∧ ¬ ((x = o ∧ y ∈ T.verts) ∨ (y = o ∧ x ∈ T.verts))) ∨
      (x ∈ T.verts ∧ y ∈ T.verts ∧ x ≠ y) := by
  simp only [State.reverse, State.Adj, mem_union, mem_sdiff,
    Triple.mem_pairs, Triple.mem_spokes]

theorem ReverseOK.adj {G : State} {T : Triple} {o : ℕ}
    (h : ReverseOK G T o) (hG : G.Valid) (x : ℕ) :
    G.Adj o x ↔ x ∈ T.verts := by
  rw [← G.mem_neighbors hG, h.2]

private theorem ReverseOK.not_center {G : State} {T : Triple} {o : ℕ}
    (h : ReverseOK G T o) (hG : G.Valid) : o ∉ T.verts :=
  fun ho => (hG ((h.adj hG o).mpr ho)).2.2 rfl

private theorem ReverseOK.verts_active {G : State} {T : Triple} {o : ℕ}
    (h : ReverseOK G T o) (hG : G.Valid) : T.verts ⊆ G.active :=
  fun _ hx => (hG ((h.adj hG _).mpr hx)).2.1

private theorem ReverseOK.degree_eq_three {G : State} {T : Triple} {o : ℕ}
    (h : ReverseOK G T o) : G.degree o = 3 := by
  simp [State.degree, h.2, Triple.card_verts]

theorem forward_valid {G : State} {T : Triple} {o : ℕ} (hG : G.Valid) :
    (G.forward T o).Valid ↔ T.verts ⊆ G.active ∧ o ∉ T.verts := by
  constructor
  · intro h
    have spoke {x : ℕ} (hx : x ∈ T.verts) : (G.forward T o).Adj o x :=
      forward_adj.mpr (Or.inr (Or.inl ⟨rfl, hx⟩))
    refine ⟨?_, fun ho => (h (spoke ho)).2.2 rfl⟩
    intro x hx
    obtain ⟨_, hxActive, hne⟩ := h (spoke hx)
    exact (mem_insert.mp hxActive).resolve_left hne.symm
  · rintro ⟨hverts, ho⟩ x y hxy
    simp only [State.forward, mem_insert]
    rw [forward_adj] at hxy
    rcases hxy with ⟨hadj, _⟩ | ⟨rfl, hy⟩ | ⟨rfl, hx⟩
    · exact ⟨Or.inr (hG hadj).1, Or.inr (hG hadj).2.1, (hG hadj).2.2⟩
    · exact ⟨Or.inl rfl, Or.inr (hverts hy), fun he => ho (he ▸ hy)⟩
    · exact ⟨Or.inr (hverts hx), Or.inl rfl, fun he => ho (he ▸ hx)⟩

theorem reverse_valid {G : State} {T : Triple} {o : ℕ}
    (hG : G.Valid) (h : ReverseOK G T o) : (G.reverse T o).Valid := by
  intro x y hxy
  simp only [State.reverse, mem_erase]
  rw [reverse_adj] at hxy
  rcases hxy with ⟨hadj, hs⟩ | ⟨hx, hy, hne⟩
  · refine ⟨⟨?_, (hG hadj).1⟩, ⟨?_, (hG hadj).2.1⟩, (hG hadj).2.2⟩
    · rintro rfl
      exact hs (Or.inl ⟨rfl, (h.adj hG y).mp hadj⟩)
    · rintro rfl
      exact hs (Or.inr ⟨rfl, (h.adj hG x).mp (State.adj_symm hadj)⟩)
  · exact ⟨⟨fun he => h.not_center hG (he ▸ hx), h.verts_active hG hx⟩,
      ⟨fun he => h.not_center hG (he ▸ hy), h.verts_active hG hy⟩, hne⟩

theorem reverse_forward_ok {G : State} {T : Triple} {o : ℕ}
    (hG : G.Valid) (h : ReverseOK G T o) : ForwardOK (G.reverse T o) T o := by
  refine ⟨?_, by simp [State.reverse], ?_⟩
  · intro x hx
    exact mem_erase.mpr ⟨fun he => h.not_center hG (he ▸ hx), h.verts_active hG hx⟩
  · exact subset_union_right

inductive Move (strong : Bool) : State → State → Prop
  | forward {G : State} (T : Triple) (o : ℕ) (ok : ForwardOK G T o) :
      Move strong G (G.forward T o)
  | reverse {G : State} (T : Triple) (o : ℕ) (ok : ReverseOK G T o)
      (independent : strong = true → Independent G T) : Move strong G (G.reverse T o)

theorem Move.valid {strong : Bool} {G H : State} (m : Move strong G H)
    (hG : G.Valid) : H.Valid := by
  cases m with
  | forward T o h => exact (forward_valid hG).mpr ⟨h.1, fun ho => h.2.1 (h.1 ho)⟩
  | reverse T o h _ => exact reverse_valid hG h

abbrev Reach (strong : Bool) := ReflTransGen (Move strong)

theorem reach_valid {strong : Bool} {G H : State} (h : Reach strong G H) (hG : G.Valid) :
    H.Valid := by
  induction h with
  | refl => exact hG
  | tail _ m ih => exact m.valid ih

theorem tri_adj {G : State} {T : Triple} {o x y : ℕ} (h : ForwardOK G T o)
    (hx : x ∈ T.verts) (hy : y ∈ T.verts) (hne : x ≠ y) : G.Adj x y :=
  h.2.2 ((T.mem_pairs x y).mpr ⟨hx, hy, hne⟩)

theorem forward_old_adj {G : State} {T : Triple} {o x y : ℕ}
    (hx : x ≠ o) (hy : y ≠ o) :
    (G.forward T o).Adj x y ↔ G.Adj x y ∧ ¬ (x ∈ T.verts ∧ y ∈ T.verts ∧ x ≠ y) := by
  simp [forward_adj, hx, hy]

theorem forward_center_adj {G : State} {T : Triple} {o y : ℕ}
    (hG : G.Valid) (h : ForwardOK G T o) :
    (G.forward T o).Adj o y ↔ y ∈ T.verts := by
  have no : ¬ G.Adj o y := fun ha => h.2.1 (hG ha).1
  have nt : o ∉ T.verts := fun hx => h.2.1 (h.1 hx)
  simp [forward_adj, no, nt]

theorem reverse_old_adj {G : State} {T : Triple} {o x y : ℕ}
    (hx : x ≠ o) (hy : y ≠ o) :
    (G.reverse T o).Adj x y ↔ G.Adj x y ∨ (x ∈ T.verts ∧ y ∈ T.verts ∧ x ≠ y) := by
  simp [reverse_adj, hx, hy]

theorem independent_iff {G : State} {T : Triple} :
    Independent G T ↔ ∀ ⦃x y⦄, x ∈ T.verts → y ∈ T.verts → x ≠ y → ¬ G.Adj x y := by
  rw [Independent, Finset.disjoint_left]
  constructor
  · intro hd x y hx hy hne ha
    exact hd ha ((T.mem_pairs x y).mpr ⟨hx, hy, hne⟩)
  · intro hi e he hpair
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hx, hy, hne⟩ := (T.mem_pairs x y).mp hpair
      exact hi hx hy hne he

private theorem forward_edges {G : State} {T : Triple} {o : ℕ}
    (hG : G.Valid) (h : ForwardOK G T o) :
    (G.forward T o).edges.card = G.edges.card := by
  have hd : Disjoint (G.edges \ T.pairs) (T.spokes o) := by
    rw [Finset.disjoint_left]
    intro e he hs
    have he' := (mem_sdiff.mp he).1
    induction e using Sym2.ind with
    | h x y =>
      rcases (T.mem_spokes o x y).mp hs with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact h.2.1 (hG he').1
      · exact h.2.1 (hG he').2.1
  have hle := card_le_card h.2.2
  rw [Triple.card_pairs] at hle
  change ((G.edges \ T.pairs) ∪ T.spokes o).card = _
  rw [card_union_of_disjoint hd, card_sdiff_of_subset h.2.2, T.card_pairs, T.card_spokes]
  omega

private theorem reverse_edges {G : State} {T : Triple} {o : ℕ}
    (hG : G.Valid) (h : ReverseOK G T o) (hi : Independent G T) :
    (G.reverse T o).edges.card = G.edges.card := by
  have hs : T.spokes o ⊆ G.edges := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rcases (T.mem_spokes o x y).mp he with ⟨rfl, hy⟩ | ⟨rfl, hx⟩
      · exact (h.adj hG y).mpr hy
      · exact State.adj_symm ((h.adj hG x).mpr hx)
  have hd : Disjoint (G.edges \ T.spokes o) T.pairs :=
    hi.mono_left sdiff_subset
  have hle := card_le_card hs
  rw [T.card_spokes] at hle
  change ((G.edges \ T.spokes o) ∪ T.pairs).card = _
  rw [card_union_of_disjoint hd, card_sdiff_of_subset hs, T.card_spokes, T.card_pairs]
  omega

private theorem strong_edge_count {G H : State} (hG : G.Valid) (m : Move true G H) :
    H.edges.card = G.edges.card := by
  cases m with
  | forward T o ok => exact forward_edges hG ok
  | reverse T o ok hi => exact reverse_edges hG ok (hi rfl)

private theorem strong_history_edge_count {G H : State} (hG : G.Valid) (h : Reach true G H) :
    H.edges.card = G.edges.card := by
  induction h with
  | refl => rfl
  | tail history m ih => exact (strong_edge_count (reach_valid history hG) m).trans ih

theorem strong_to_ordinary {G H : State} (h : Reach true G H) : Reach false G H := by
  refine ReflTransGen.mono (r := Move true) (p := Move false) ?_ G H h
  intro G H m
  cases m with
  | forward T o ok => exact Move.forward T o ok
  | reverse T o ok _ => exact Move.reverse T o ok (fun h => by contradiction)

def State.graph (G : State) (hG : G.Valid) : SimpleGraph ↥G.active where
  Adj x y := G.Adj x y
  symm := ⟨fun _ _ => State.adj_symm⟩
  loopless := ⟨fun _ h => (hG h).2.2 rfl⟩

instance (G : State) (hG : G.Valid) : DecidableRel (G.graph hG).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y))

@[simp] private theorem State.graph_adj {G : State} {hG : G.Valid} (x y : ↥G.active) :
    (G.graph hG).Adj x y ↔ G.Adj x y := Iff.rfl

private def State.vertexEmbedding (G : State) : ↥G.active ↪ ℕ :=
  ⟨Subtype.val, Subtype.val_injective⟩

private theorem graph_neighbors {G : State} (hG : G.Valid) (x : ↥G.active) :
    ((G.graph hG).neighborFinset x).map G.vertexEmbedding = G.neighbors x := by
  classical
  ext y
  rw [mem_map, State.mem_neighbors hG]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (SimpleGraph.mem_neighborFinset _ _ _).mp hz
  · intro ha
    exact ⟨⟨y, (hG ha).2.1⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr ha, rfl⟩

private theorem graph_degree {G : State} (hG : G.Valid) (x : ↥G.active) :
    (G.graph hG).degree x = G.degree x := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, State.degree, ← graph_neighbors hG, card_map]

private theorem graph_edges {G : State} (hG : G.Valid) :
    (G.graph hG).edgeFinset.map (G.vertexEmbedding.sym2Map) = G.edges := by
  classical
  ext e
  rw [mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    induction f using Sym2.ind with
    | h x y =>
      exact SimpleGraph.mem_edgeFinset.mp hf
  · intro he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hx, hy, _⟩ := hG he
      exact ⟨s(⟨x, hx⟩, ⟨y, hy⟩), SimpleGraph.mem_edgeFinset.mpr he, rfl⟩

private theorem graph_edge_count {G : State} (hG : G.Valid) :
    (G.graph hG).edgeFinset.card = G.edges.card := by
  rw [← graph_edges hG, card_map]

structure Site (V : Type*) where
  a : V
  b : V
  c : V
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c

def Site.Has {V : Type*} (T : Site V) (x : V) : Prop := x = T.a ∨ x = T.b ∨ x = T.c

private def Site.map {A B : Type*} (T : Site A) (e : A ↪ B) : Site B :=
  ⟨e T.a, e T.b, e T.c, fun h => T.ab (e.injective h),
    fun h => T.ac (e.injective h), fun h => T.bc (e.injective h)⟩

@[simp] private theorem Site.has_map {A B : Type*} (T : Site A) (e : A ↪ B) (x : A) :
    (T.map e).Has (e x) ↔ T.Has x := by
  simp [Site.Has, Site.map, e.injective.eq_iff]

private def Site.labels {V : Type*} (T : Site V) (e : V ↪ ℕ) : Triple :=
  let U := T.map e
  ⟨U.a, U.b, U.c, U.ab, U.ac, U.bc⟩

@[simp] private theorem Site.mem_labels {V : Type*} (T : Site V) (e : V ↪ ℕ) (x : V) :
    e x ∈ (T.labels e).verts ↔ T.Has x := by
  rw [Triple.mem_verts]
  exact T.has_map e x

-- The Option equivalence says exactly which vertices survive and identifies the center.
structure ForwardSpec {A B : Type*} (G : SimpleGraph A) (H : SimpleGraph B) where
  T : Site A
  place : Option A ≃ B
  triangle : ∀ x y, T.Has x → T.Has y → x ≠ y → G.Adj x y
  old_old : ∀ x y, H.Adj (place (some x)) (place (some y)) ↔
    G.Adj x y ∧ ¬ (T.Has x ∧ T.Has y ∧ x ≠ y)
  center : ∀ x, H.Adj (place none) (place (some x)) ↔ T.Has x

structure ReverseSpec {A B : Type*} (G : SimpleGraph A) (H : SimpleGraph B) where
  T : Site B
  place : Option B ≃ A
  center : ∀ x, G.Adj (place none) (place (some x)) ↔ T.Has x
  old_old : ∀ x y, H.Adj x y ↔
    G.Adj (place (some x)) (place (some y)) ∨ (T.Has x ∧ T.Has y ∧ x ≠ y)

def ReverseSpec.Independent {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (m : ReverseSpec G H) : Prop :=
  ∀ x y, m.T.Has x → m.T.Has y → x ≠ y → ¬ G.Adj (m.place (some x)) (m.place (some y))

def GraphMove {A B : Type*} (strong : Bool) (G : SimpleGraph A) (H : SimpleGraph B) : Prop :=
  Nonempty (ForwardSpec G H) ∨ ∃ m : ReverseSpec G H, strong = true → m.Independent

@[simp] private theorem Site.has_map_iso {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (T : Site A) (e : G ≃g H) (x : A) :
    (T.map e.toEquiv.toEmbedding).Has (e x) ↔ T.Has x := T.has_map e.toEquiv.toEmbedding x

theorem GraphMove.transport {A B A' B' : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    {G' : SimpleGraph A'} {H' : SimpleGraph B'} (e : G ≃g G') (f : H ≃g H')
    {strong : Bool} (m : GraphMove strong G H) : GraphMove strong G' H' := by
  rcases m with ⟨⟨m⟩⟩ | ⟨m, hm⟩
  · let p := (e.toEquiv.symm.optionCongr.trans m.place).trans f.toEquiv
    have cancel (x : A) : e.toEquiv.symm (e x) = x := e.toEquiv.symm_apply_apply x
    left
    refine ⟨⟨m.T.map e.toEquiv.toEmbedding, p, ?_, ?_, ?_⟩⟩
    · intro x y
      obtain ⟨x, rfl⟩ := e.toEquiv.surjective x
      obtain ⟨y, rfl⟩ := e.toEquiv.surjective y
      simpa only [Site.has_map_iso, RelIso.coe_fn_toEquiv,
        e.injective.ne_iff, e.map_adj_iff] using m.triangle x y
    · intro x y
      obtain ⟨x, rfl⟩ := e.toEquiv.surjective x
      obtain ⟨y, rfl⟩ := e.toEquiv.surjective y
      simpa only [p, Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_some,
        RelIso.coe_fn_toEquiv, cancel,
        Site.has_map_iso, e.injective.ne_iff, e.map_adj_iff, f.map_adj_iff] using m.old_old x y
    · intro x
      obtain ⟨x, rfl⟩ := e.toEquiv.surjective x
      simpa only [p, Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_none,
        Option.map_some, RelIso.coe_fn_toEquiv, cancel, Site.has_map_iso, f.map_adj_iff]
        using m.center x
  · let p := (f.toEquiv.symm.optionCongr.trans m.place).trans e.toEquiv
    have cancel (x : B) : f.toEquiv.symm (f x) = x := f.toEquiv.symm_apply_apply x
    right
    let m' : ReverseSpec G' H' := {
      T := m.T.map f.toEquiv.toEmbedding
      place := p
      center := by
        intro x
        obtain ⟨x, rfl⟩ := f.toEquiv.surjective x
        simpa only [p, Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_none,
          Option.map_some, Site.has_map_iso, RelIso.coe_fn_toEquiv, cancel,
          e.map_adj_iff] using m.center x
      old_old := by
        intro x y
        obtain ⟨x, rfl⟩ := f.toEquiv.surjective x
        obtain ⟨y, rfl⟩ := f.toEquiv.surjective y
        simpa only [p, Equiv.trans_apply, Equiv.optionCongr_apply,
          Option.map_some, Site.has_map_iso, RelIso.coe_fn_toEquiv, cancel,
          e.map_adj_iff, f.map_adj_iff, f.injective.ne_iff] using m.old_old x y
    }
    refine ⟨m', fun hs => ?_⟩
    intro x y
    obtain ⟨x, rfl⟩ := f.toEquiv.surjective x
    obtain ⟨y, rfl⟩ := f.toEquiv.surjective y
    simpa only [m', p, Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_some,
      Site.has_map_iso, RelIso.coe_fn_toEquiv, cancel, e.map_adj_iff, f.injective.ne_iff]
      using hm hs x y

private def forwardApex {G : State} {T : Triple} (o : ℕ) : ↥(G.forward T o).active :=
  ⟨o, mem_insert_self _ _⟩

private def forwardSurvivors {G : State} {T : Triple} {o : ℕ} (ho : o ∉ G.active) :
    ↥G.active ≃ {x : ↥(G.forward T o).active // x ≠ forwardApex o} where
  toFun x := ⟨⟨x, mem_insert_of_mem x.2⟩,
    fun he => ho ((show x.val = o from congrArg Subtype.val he) ▸ x.2)⟩
  invFun x := ⟨x.1.1, (mem_insert.mp x.1.2).resolve_left (fun h => x.2 (Subtype.ext h))⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def forwardLabels {G : State} {T : Triple} {o : ℕ} (ho : o ∉ G.active) :
    Option ↥G.active ≃ ↥(G.forward T o).active :=
  ((Equiv.optionSubtype (forwardApex o)).symm (forwardSurvivors ho)).1

@[simp] private theorem forwardLabels_some {G : State} {T : Triple} {o : ℕ} (ho : o ∉ G.active)
    (x : ↥G.active) : (forwardLabels (T := T) ho (some x)).val = x.val := rfl

private def reverseCenter {G : State} {o : ℕ} (ho : o ∈ G.active) : ↥G.active := ⟨o, ho⟩

private def reverseSurvivors {G : State} {T : Triple} {o : ℕ} (ho : o ∈ G.active) :
    ↥(G.reverse T o).active ≃ {x : ↥G.active // x ≠ reverseCenter ho} where
  toFun x := ⟨⟨x, mem_of_mem_erase x.2⟩, fun he => (mem_erase.mp x.2).1 (congrArg Subtype.val he)⟩
  invFun x := ⟨x.1.1, mem_erase.mpr ⟨fun he => x.2 (Subtype.ext he), x.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def reverseLabels {G : State} {T : Triple} {o : ℕ} (ho : o ∈ G.active) :
    Option ↥(G.reverse T o).active ≃ ↥G.active :=
  ((Equiv.optionSubtype (reverseCenter ho)).symm (reverseSurvivors ho)).1

private def Triple.restrict (T : Triple) {S : Finset ℕ} (h : T.verts ⊆ S) : Site ↥S :=
  ⟨⟨T.a, h (by simp [Triple.mem_verts])⟩, ⟨T.b, h (by simp [Triple.mem_verts])⟩,
    ⟨T.c, h (by simp [Triple.mem_verts])⟩, fun he => T.ab (congrArg Subtype.val he),
    fun he => T.ac (congrArg Subtype.val he), fun he => T.bc (congrArg Subtype.val he)⟩

@[simp] private theorem Triple.has_restrict {S : Finset ℕ} (T : Triple) (h : T.verts ⊆ S) (x : ↥S) :
    (T.restrict h).Has x ↔ x.val ∈ T.verts := by
  simp [Triple.restrict, Site.Has, Triple.mem_verts, Subtype.ext_iff]

private theorem realize_forward {G : State} {T : Triple} {o : ℕ} {strong : Bool}
    (hG : G.Valid) (h : ForwardOK G T o) :
    GraphMove strong (G.graph hG) ((G.forward T o).graph
      ((forward_valid hG).mpr ⟨h.1, fun ho => h.2.1 (h.1 ho)⟩)) := by
  left
  refine ⟨⟨T.restrict h.1, forwardLabels h.2.1, ?_, ?_, ?_⟩⟩
  · intro x y hx hy hne
    exact tri_adj h ((T.has_restrict h.1 x).mp hx) ((T.has_restrict h.1 y).mp hy)
      (fun he => hne (Subtype.ext he))
  · intro x y
    simpa only [State.graph_adj, forwardLabels_some, Triple.has_restrict, Subtype.coe_ne_coe] using
      (forward_old_adj (G := G) (T := T) (o := o)
        (fun he => h.2.1 (he ▸ x.2)) (fun he => h.2.1 (he ▸ y.2)))
  · intro x
    change (G.forward T o).Adj o x.val ↔ (T.restrict h.1).Has x
    simpa only [Triple.has_restrict] using forward_center_adj (y := x.val) hG h

private theorem realize_reverse {G : State} {T : Triple} {o : ℕ} {strong : Bool}
    (hG : G.Valid) (h : ReverseOK G T o) (hi : strong = true → Independent G T) :
    GraphMove strong (G.graph hG) ((G.reverse T o).graph (reverse_valid hG h)) := by
  have hT : T.verts ⊆ (G.reverse T o).active := (reverse_forward_ok hG h).1
  right
  let m : ReverseSpec (G.graph hG) ((G.reverse T o).graph (reverse_valid hG h)) := {
    T := T.restrict hT
    place := reverseLabels h.1
    center := by
      intro x
      change G.Adj o x.val ↔ (T.restrict hT).Has x
      simpa only [Triple.has_restrict] using h.adj hG x.val
    old_old := by
      intro x y
      change (G.reverse T o).Adj x.val y.val ↔
        G.Adj x.val y.val ∨ ((T.restrict hT).Has x ∧ (T.restrict hT).Has y ∧ x ≠ y)
      simpa only [Triple.has_restrict, Subtype.coe_ne_coe]
        using (reverse_old_adj (G := G) (T := T) (o := o) (mem_erase.mp x.2).1 (mem_erase.mp y.2).1)
  }
  refine ⟨m, fun hs x y hx hy hne => ?_⟩
  apply independent_iff.mp (hi hs) ((T.has_restrict hT x).mp hx) ((T.has_restrict hT y).mp hy)
    (fun he => hne (Subtype.ext he))

theorem realize_move {G H : State} {strong : Bool} (hG : G.Valid) (m : Move strong G H) :
    GraphMove strong (G.graph hG) (H.graph (m.valid hG)) := by
  cases m with
  | forward T o ok => exact realize_forward hG ok
  | reverse T o ok hi => exact realize_reverse hG ok hi

private theorem Site.exists_label_of_mem {A : Type*} (T : Site A) (e : A ↪ ℕ) {x : ℕ}
    (hx : x ∈ (T.labels e).verts) : ∃ a : A, e a = x ∧ T.Has a := by
  rw [Triple.mem_verts] at hx
  change x = e T.a ∨ x = e T.b ∨ x = e T.c at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨T.a, rfl, Or.inl rfl⟩
  · exact ⟨T.b, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨T.c, rfl, Or.inr (Or.inr rfl)⟩

private theorem lift_forward {G : State} {B : Type*} {H : SimpleGraph B}
    (hG : G.Valid) (m : ForwardSpec (G.graph hG) H) {o : ℕ} (ho : o ∉ G.active) :
    ∃ ok : ForwardOK G (m.T.labels G.vertexEmbedding) o,
      Nonempty (H ≃g (G.forward (m.T.labels G.vertexEmbedding) o).graph
        ((forward_valid hG).mpr ⟨ok.1, fun ht => ok.2.1 (ok.1 ht)⟩)) := by
  let T := m.T.labels G.vertexEmbedding
  have ht : T.verts ⊆ G.active := by
    intro x hx
    obtain ⟨a, rfl, _⟩ := m.T.exists_label_of_mem G.vertexEmbedding hx
    exact a.2
  have ok : ForwardOK G T o := by
    refine ⟨ht, ho, ?_⟩
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hx, hy, hne⟩ := (T.mem_pairs x y).mp he
      obtain ⟨a, rfl, ha⟩ := m.T.exists_label_of_mem G.vertexEmbedding hx
      obtain ⟨b, rfl, hb⟩ := m.T.exists_label_of_mem G.vertexEmbedding hy
      exact m.triangle a b ha hb (fun he => hne (congrArg G.vertexEmbedding he))
  refine ⟨ok, ⟨{ toEquiv := m.place.symm.trans (forwardLabels ho), map_rel_iff' := ?_ }⟩⟩
  intro x y
  obtain ⟨x, rfl⟩ := m.place.surjective x
  obtain ⟨y, rfl⟩ := m.place.surjective y
  change
    (G.forward T o).Adj (forwardLabels ho (m.place.symm (m.place x))).val
      (forwardLabels ho (m.place.symm (m.place y))).val ↔ H.Adj (m.place x) (m.place y)
  simp only [Equiv.symm_apply_apply]
  cases x with
  | none =>
    cases y with
    | none =>
      change (G.forward T o).Adj o o ↔ H.Adj (m.place none) (m.place none)
      have hForward : (G.forward T o).Valid :=
        (forward_valid hG).mpr ⟨ok.1, fun ht => ho (ok.1 ht)⟩
      exact iff_of_false (fun h => (hForward h).2.2 rfl) (fun h => H.irrefl h)
    | some y =>
      change (G.forward T o).Adj o y.val ↔ H.Adj (m.place none) (m.place (some y))
      rw [forward_center_adj hG ok, m.center]
      exact m.T.mem_labels G.vertexEmbedding y
  | some x =>
    cases y with
    | none =>
      change (G.forward T o).Adj x.val o ↔ H.Adj (m.place (some x)) (m.place none)
      rw [show (G.forward T o).Adj x.val o ↔ (G.forward T o).Adj o x.val from
        ⟨State.adj_symm, State.adj_symm⟩, forward_center_adj hG ok, H.adj_comm, m.center]
      exact m.T.mem_labels G.vertexEmbedding x
    | some y =>
      rw [forwardLabels_some, forwardLabels_some,
        forward_old_adj (G := G) (T := T) (o := o) (x := x.val) (y := y.val)
          (fun he => ho (he ▸ x.2)) (fun he => ho (he ▸ y.2)), m.old_old]
      change G.Adj x.val y.val ∧ ¬ (G.vertexEmbedding x ∈ T.verts ∧
          G.vertexEmbedding y ∈ T.verts ∧ x.val ≠ y.val) ↔ _
      rw [m.T.mem_labels G.vertexEmbedding x, m.T.mem_labels G.vertexEmbedding y,
        Subtype.coe_ne_coe]
      rfl

private def reverseSiteEmbedding {G : State} {B : Type*} (p : Option B ≃ ↥G.active) : B ↪ ℕ :=
  ⟨fun x => (p (some x)).val,
    fun _ _ h => Option.some.inj (p.injective (Subtype.ext h))⟩

private theorem reverseSiteEmbedding_ne {G : State} {B : Type*} (p : Option B ≃ ↥G.active) (x : B) :
    reverseSiteEmbedding p x ≠ (p none).val :=
  fun h => nomatch p.injective (Subtype.ext h : p (some x) = p none)

theorem lift_reverse {G : State} {B : Type*} {H : SimpleGraph B}
    (hG : G.Valid) (m : ReverseSpec (G.graph hG) H) :
    let T := m.T.labels (reverseSiteEmbedding m.place)
    let o := (m.place none).val
    ∃ ok : ReverseOK G T o,
      (Independent G T ↔ m.Independent) ∧
      Nonempty (H ≃g (G.reverse T o).graph (reverse_valid hG ok)) := by
  let e := reverseSiteEmbedding m.place
  let T := m.T.labels e
  let o := (m.place none).val
  have ho : o ∈ G.active := (m.place none).2
  have ht : T.verts ⊆ G.active := by
    intro x hx
    obtain ⟨a, rfl, _⟩ := m.T.exists_label_of_mem e hx
    exact (m.place (some a)).2
  have hne : ∀ x ∈ T.verts, x ≠ o := by
    intro x hx
    obtain ⟨a, rfl, _⟩ := m.T.exists_label_of_mem e hx
    exact reverseSiteEmbedding_ne m.place a
  have ok : ReverseOK G T o := by
    refine ⟨ho, ?_⟩
    ext x
    rw [State.mem_neighbors hG]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := m.place.surjective ⟨x, (hG hx).2.1⟩
      have hv : (m.place a).val = x := congrArg Subtype.val ha
      cases a with
      | none => exact False.elim ((hG hx).2.2 hv)
      | some a =>
        change e a = x at hv
        rw [← hv] at hx ⊢
        exact (m.T.mem_labels e a).mpr ((m.center a).mp hx)
    · intro hx
      obtain ⟨a, rfl, ha⟩ := m.T.exists_label_of_mem e hx
      exact (m.center a).mpr ha
  refine ⟨ok, ?_, ?_⟩
  · rw [independent_iff]
    constructor
    · intro hi x y hx hy hxy
      exact hi ((m.T.mem_labels e x).mpr hx) ((m.T.mem_labels e y).mpr hy)
        (fun he => hxy (e.injective he))
    · intro hi x y hx hy hxy
      obtain ⟨a, rfl, ha⟩ := m.T.exists_label_of_mem e hx
      obtain ⟨b, rfl, hb⟩ := m.T.exists_label_of_mem e hy
      exact hi a b ha hb (fun he => hxy (congrArg e he))
  · let out : B → ↥(G.reverse T o).active := fun a =>
      ⟨e a, mem_erase.mpr ⟨reverseSiteEmbedding_ne m.place a, (m.place (some a)).2⟩⟩
    have hinj : Function.Injective out := fun _ _ he =>
      e.injective (congrArg (fun z : ↥(G.reverse T o).active => z.val) he)
    have hsurj : Function.Surjective out := by
      intro x
      obtain ⟨a, ha⟩ := m.place.surjective ⟨x.val, (mem_erase.mp x.2).2⟩
      have hv : (m.place a).val = x.val := congrArg Subtype.val ha
      cases a with
      | none => exact False.elim ((mem_erase.mp x.2).1 hv.symm)
      | some a => exact ⟨a, Subtype.ext hv⟩
    refine ⟨{ toEquiv := Equiv.ofBijective out ⟨hinj, hsurj⟩, map_rel_iff' := ?_ }⟩
    intro x y
    change (G.reverse T o).Adj (e x) (e y) ↔ H.Adj x y
    rw [reverse_old_adj (reverseSiteEmbedding_ne m.place x) (reverseSiteEmbedding_ne m.place y),
      m.T.mem_labels e x, m.T.mem_labels e y, e.injective.ne_iff, m.old_old]
    rfl

theorem lift_move {G : State} {A B : Type*} {F : SimpleGraph A} {H : SimpleGraph B}
    (hG : G.Valid) (i : F ≃g G.graph hG) {strong : Bool} (m : GraphMove strong F H) :
    ∃ K : State, ∃ step : Move strong G K, Nonempty (H ≃g K.graph (step.valid hG)) := by
  rcases m.transport i SimpleGraph.Iso.refl with ⟨⟨f⟩⟩ | ⟨r, hr⟩
  · obtain ⟨o, ho⟩ := Infinite.exists_notMem_finset G.active
    obtain ⟨ok, e⟩ := lift_forward hG f ho
    exact ⟨_, Move.forward _ _ ok, e⟩
  · obtain ⟨ok, hInd, e⟩ := lift_reverse hG r
    exact ⟨_, Move.reverse _ _ ok (fun hs => hInd.mpr (hr hs)), e⟩

theorem every_finite_graph_realized {A : Type*} [Finite A] (F : SimpleGraph A) :
    ∃ G : State, ∃ hG : G.Valid, Nonempty (F ≃g G.graph hG) := by
  classical
  let := Fintype.ofFinite A
  let e : A ↪ ℕ := (Fintype.equivFin A).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩
  let G : State := ⟨univ.map e, F.edgeFinset.map e.sym2Map⟩
  have ha (x : A) : e x ∈ G.active := mem_map.mpr ⟨x, mem_univ _, rfl⟩
  have hG : G.Valid := by
    intro x y h
    change s(x, y) ∈ F.edgeFinset.map e.sym2Map at h
    obtain ⟨w, hw, he⟩ := mem_map.mp h
    induction w using Sym2.ind with
    | h a b =>
      have hab : F.Adj a b := SimpleGraph.mem_edgeFinset.mp hw
      have hne := e.injective.ne (F.ne_of_adj hab)
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ha a, ha b, hne⟩
      · exact ⟨ha b, ha a, hne.symm⟩
  let toLabel : A → ↥G.active := fun x => ⟨e x, ha x⟩
  have hinj : Function.Injective toLabel := fun _ _ h =>
    e.injective (congrArg (fun z : ↥G.active => z.val) h)
  have hsurj : Function.Surjective toLabel := by
    intro x
    obtain ⟨a, _, h⟩ := mem_map.mp x.2
    exact ⟨a, Subtype.ext h⟩
  refine ⟨G, hG, ⟨{ toEquiv := Equiv.ofBijective toLabel ⟨hinj, hsurj⟩, map_rel_iff' := ?_ }⟩⟩
  intro a b
  change e.sym2Map s(a, b) ∈ F.edgeFinset.map e.sym2Map ↔ F.Adj a b
  rw [mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    exact SimpleGraph.mem_edgeFinset.mp (e.sym2Map.injective he ▸ hw)
  · intro he
    exact ⟨_, SimpleGraph.mem_edgeFinset.mpr he, rfl⟩

structure FiniteGraph where
  V : Type u
  graph : SimpleGraph V
  finiteV : Finite V

attribute [instance] FiniteGraph.finiteV

noncomputable def FiniteGraph.Degree (G : FiniteGraph) (x : G.V) : ℕ :=
  Nat.card ↥(G.graph.neighborSet x)

def FiniteGraph.MinDegree (G : FiniteGraph) (d : ℕ) : Prop := ∀ x : G.V, d ≤ G.Degree x

noncomputable def FiniteGraph.edgeCount (G : FiniteGraph) : ℕ := Nat.card ↥G.graph.edgeSet

theorem finiteGraph_iso_edges {G : FiniteGraph.{u}} {H : FiniteGraph.{v}}
    (e : G.graph ≃g H.graph) : G.edgeCount = H.edgeCount :=
  Nat.card_congr e.mapEdgeSet

def State.asFiniteGraph (G : State) (hG : G.Valid) : FiniteGraph.{u} :=
  ⟨ULift.{u} ↥G.active, (G.graph hG).comap ULift.down, inferInstance⟩

def asFiniteGraph_iso {G : State} (hG : G.Valid) :
    (G.asFiniteGraph.{u} hG).graph ≃g G.graph hG :=
  SimpleGraph.Iso.comap Equiv.ulift (G.graph hG)

theorem iso_degree_of_state {A : Type*} {F : SimpleGraph A} {G : State} (hG : G.Valid)
    (e : F ≃g G.graph hG) (x : A) :
    Nat.card ↥(F.neighborSet x) = G.degree (e x).val := by
  calc
    Nat.card ↥(F.neighborSet x) = Nat.card ↥((G.graph hG).neighborSet (e x)) :=
      Nat.card_congr (e.mapNeighborSet x)
    _ = (G.graph hG).degree (e x) := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
    _ = G.degree (e x).val := graph_degree hG (e x)

theorem iso_edges_of_state {A : Type*} {F : SimpleGraph A} {G : State} (hG : G.Valid)
    (e : F ≃g G.graph hG) : Nat.card ↥F.edgeSet = G.edges.card := by
  calc
    Nat.card ↥F.edgeSet = Nat.card ↥(G.graph hG).edgeSet := Nat.card_congr e.mapEdgeSet
    _ = (G.graph hG).edgeFinset.card := by
      simp [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset]
    _ = G.edges.card := graph_edge_count hG

abbrev SourceMove (strong : Bool) (G H : FiniteGraph.{u}) := GraphMove strong G.graph H.graph

abbrev SourceReach (strong : Bool) := ReflTransGen (SourceMove.{u} strong)

def SourceFamily (strong : Bool) (G H : FiniteGraph.{u}) : Prop :=
  ∃ K : FiniteGraph.{u}, SourceReach strong G K ∧ Nonempty (K.graph ≃g H.graph)

private theorem realize_source_move {G H : State} {strong : Bool} (hG : G.Valid)
    (m : Move strong G H) :
    SourceMove strong (G.asFiniteGraph.{u} hG) (H.asFiniteGraph.{u} (m.valid hG)) :=
  (realize_move hG m).transport (asFiniteGraph_iso hG).symm
    (asFiniteGraph_iso (m.valid hG)).symm

theorem realize_source_history {G H : State} {strong : Bool} (hG : G.Valid)
    (h : Reach strong G H) :
    SourceReach strong (G.asFiniteGraph.{u} hG) (H.asFiniteGraph.{u} (reach_valid h hG)) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail history m ih => exact ih.tail (realize_source_move (reach_valid history hG) m)

private theorem lift_source_history {G H : FiniteGraph.{u}} {strong : Bool}
    (h : SourceReach strong G H) {S : State} (hS : S.Valid) (e : G.graph ≃g S.graph hS) :
    ∃ T : State, ∃ history : Reach strong S T,
      Nonempty (H.graph ≃g T.graph (reach_valid history hS)) := by
  induction h with
  | refl => exact ⟨S, ReflTransGen.refl, ⟨e⟩⟩
  | tail _ m ih =>
    obtain ⟨_, history, ⟨i⟩⟩ := ih
    obtain ⟨_, step, target⟩ := lift_move (reach_valid history hS) i m
    exact ⟨_, history.tail step, target⟩

def ReverseSpec.relabelSource {A B A' : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    {G' : SimpleGraph A'} (m : ReverseSpec G H) (e : G ≃g G') : ReverseSpec G' H :=
  ⟨m.T, m.place.trans e.toEquiv, fun x => e.map_adj_iff.trans (m.center x),
    fun x y => (m.old_old x y).trans (or_congr e.map_adj_iff.symm Iff.rfl)⟩

theorem ReverseSpec.relabelSource_independent {A B A' : Type*} {G : SimpleGraph A}
    {H : SimpleGraph B} {G' : SimpleGraph A'} (m : ReverseSpec G H) (e : G ≃g G') :
    (m.relabelSource e).Independent ↔ m.Independent := by
  constructor
  · intro h x y hx hy hne ha
    exact h x y hx hy hne (e.map_adj_iff.mpr ha)
  · intro h x y hx hy hne ha
    exact h x y hx hy hne (e.map_adj_iff.mp ha)

theorem source_reverse_degree_three {G : FiniteGraph.{u}} {H : FiniteGraph.{v}}
    (m : ReverseSpec G.graph H.graph) : G.Degree (m.place none) = 3 := by
  obtain ⟨S, hS, ⟨e⟩⟩ := every_finite_graph_realized G.graph
  obtain ⟨h, _, _⟩ := lift_reverse hS (m.relabelSource e)
  exact (iso_degree_of_state hS e (m.place none)).trans h.degree_eq_three


theorem source_strong_to_ordinary {G H : FiniteGraph.{u}} (h : SourceReach true G H) :
    SourceReach false G H := by
  refine ReflTransGen.mono (r := SourceMove true) (p := SourceMove false) ?_ G H h
  intro G H m
  rcases m with hf | ⟨m, _⟩
  · exact Or.inl hf
  · exact Or.inr ⟨m, fun h => by contradiction⟩

theorem source_strong_edge_count {G H : FiniteGraph.{u}} (h : SourceReach true G H) :
    H.edgeCount = G.edgeCount := by
  obtain ⟨S, hS, ⟨i⟩⟩ := every_finite_graph_realized G.graph
  obtain ⟨T, history, ⟨j⟩⟩ := lift_source_history h hS i
  exact (iso_edges_of_state (reach_valid history hS) j).trans
    ((strong_history_edge_count hS history).trans (iso_edges_of_state hS i).symm)

end DeltaY
