/- GID: D5/S3/Combinatorics/Graph/Walks/AmoebaHost
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/AmoebaHost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Finite layered trees with a preserved core and controlled branching degrees. -/

import D5.S3.Combinatorics.Graph.Walks.AmoebaConfinement

namespace D5.S3.Combinatorics.Graph.Walks.AmoebaConfinement

open SimpleGraph
open scoped BigOperators
noncomputable section
open Classical

/-- Attach each new leaf to its specified old parent. -/
def sprout {V L : Type} (G : SimpleGraph V) (parent : L → V) : SimpleGraph (V ⊕ L) where
  Adj x y := match x, y with
    | .inl v, .inl w => G.Adj v w
    | .inl v, .inr a => v = parent a
    | .inr a, .inl v => v = parent a
    | .inr _, .inr _ => False
  symm.symm := by
    intro x y h
    cases x <;> cases y
    · exact h.symm
    · exact h
    · exact h
    · exact h
  loopless.irrefl := by
    intro x
    cases x
    · exact G.irrefl
    · exact id

private def sproutCore {V L : Type} (G : SimpleGraph V) (p : L → V) : Copy G (sprout G p) where
  toHom := ⟨Sum.inl, fun h => h⟩
  injective' := Sum.inl_injective

private def sproutEdge {V L : Type} (G : SimpleGraph V) (p : L → V) :
    G.edgeSet ⊕ L → (sprout G p).edgeSet
  | .inl e => (sproutCore G p).mapEdgeSet e
  | .inr a => ⟨s(Sum.inl (p a), Sum.inr a), rfl⟩

private theorem sproutEdge_bijective {V L : Type} (G : SimpleGraph V) (p : L → V) :
    Function.Bijective (sproutEdge G p) := by
  constructor
  · intro x y h
    cases x with
    | inl e =>
      cases y with
      | inl f =>
        exact congrArg Sum.inl ((sproutCore G p).mapEdgeSet.injective h)
      | inr b =>
        obtain ⟨e, he⟩ := e
        induction e using Sym2.ind with
        | _ v w =>
          have hh := congrArg Subtype.val h
          simp [sproutEdge, sproutCore, Copy.mapEdgeSet, Hom.mapEdgeSet, Sym2.eq_iff] at hh
    | inr a =>
      cases y with
      | inl e =>
        obtain ⟨e, he⟩ := e
        induction e using Sym2.ind with
        | _ v w =>
          have hh := congrArg Subtype.val h
          simp [sproutEdge, sproutCore, Copy.mapEdgeSet, Hom.mapEdgeSet, Sym2.eq_iff] at hh
      | inr b =>
        have hh := congrArg Subtype.val h
        simp only [sproutEdge, Sym2.eq_iff] at hh
        rcases hh with hh | hh
        · exact congrArg Sum.inr (Sum.inr.inj hh.2)
        · cases hh.1
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ x y =>
      cases x with
      | inl v =>
        cases y with
        | inl w => exact ⟨.inl ⟨s(v, w), he⟩, rfl⟩
        | inr a =>
          change v = p a at he
          subst v
          exact ⟨.inr a, rfl⟩
      | inr a =>
        cases y with
        | inl v =>
          change v = p a at he
          subst v
          exact ⟨.inr a, Subtype.ext Sym2.eq_swap⟩
        | inr b => exact he.elim

private theorem sprout_tree {V L : Type} [Fintype V] [Fintype L]
    {G : SimpleGraph V} (hG : G.IsTree) (p : L → V) : (sprout G p).IsTree := by
  let K := sprout G p
  have hc : K.Connected := by
    haveI : Nonempty V := hG.connected.nonempty
    haveI : Nonempty (V ⊕ L) := ⟨.inl (Classical.choice ‹Nonempty V›)⟩
    constructor
    intro x y
    have toCore : ∀ x : V ⊕ L, ∃ v, K.Reachable x (.inl v) := by
      intro x
      cases x with
      | inl v => exact ⟨v, .refl _⟩
      | inr a => exact ⟨p a, (show K.Adj (.inr a) (.inl (p a)) from rfl).reachable⟩
    obtain ⟨v, hv⟩ := toCore x
    obtain ⟨w, hw⟩ := toCore y
    exact hv.trans (((hG.connected.preconnected v w).map (sproutCore G p).toHom).trans hw.symm)
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  have he := Fintype.card_congr (Equiv.ofBijective (sproutEdge G p) (sproutEdge_bijective G p))
  have hGcard := (isTree_iff_connected_and_card.mp hG).2
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum] at *
  omega

private def sproutNeighborEquiv {V L : Type} (G : SimpleGraph V) (p : L → V) (v : V) :
    (sprout G p).neighborSet (.inl v) ≃ (G.neighborSet v ⊕ {a : L // v = p a}) where
  toFun x := match x with
    | ⟨.inl w, hw⟩ => .inl ⟨w, hw⟩
    | ⟨.inr a, ha⟩ => .inr ⟨a, ha⟩
  invFun x := match x with
    | .inl ⟨w, hw⟩ => ⟨.inl w, hw⟩
    | .inr ⟨a, ha⟩ => ⟨.inr a, ha⟩
  left_inv := by rintro ⟨x, hx⟩; cases x <;> rfl
  right_inv := by rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> rfl

private theorem sprout_degree_core {V L : Type} [Fintype V] [Fintype L]
    (G : SimpleGraph V) (p : L → V) (v : V) :
    (sprout G p).degree (.inl v) = G.degree v + Fintype.card {a : L // v = p a} := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  simpa using Fintype.card_congr (sproutNeighborEquiv G p v)

private theorem sprout_degree_leaf {V L : Type} [Fintype V] [Fintype L]
    (G : SimpleGraph V) (p : L → V) (a : L) : (sprout G p).degree (.inr a) = 1 := by
  rw [← ncard_neighborSet]
  have hs : (sprout G p).neighborSet (.inr a) = {Sum.inl (p a)} := by
    ext x
    cases x <;> simp [neighborSet, sprout]
  rw [hs, Set.ncard_singleton]

private def selectedFiberEquiv {V : Type} (B : Set V) (b : ℕ) (v : V) (hv : v ∈ B) :
    {a : B × Fin b // v = a.1.val} ≃ Fin b where
  toFun a := a.val.2
  invFun j := ⟨(⟨v, hv⟩, j), rfl⟩
  left_inv := by
    rintro ⟨⟨⟨w, hw⟩, j⟩, h⟩
    dsimp at h
    subst w
    rfl
  right_inv _ := rfl

private theorem selectedFiber_card {V : Type} [Fintype V] (B : Set V) (b : ℕ) (v : V) :
    Nat.card {a : B × Fin b // v = a.1.val} = if v ∈ B then b else 0 := by
  split_ifs with hv
  · simpa using Nat.card_congr (selectedFiberEquiv B b v hv)
  · haveI : IsEmpty {a : B × Fin b // v = a.1.val} :=
      ⟨fun a => hv (a.property ▸ a.val.1.property)⟩
    simp

/-- A core-preserving finite tree with leaves only at its outermost layer. -/
structure Layered (T : Host) (M q N : ℕ) where
  host : Host
  core : Copy T.graph host.graph
  level : host.Vertex → ℕ
  core_level : ∀ v, level (core v) = 0
  zero_core : ∀ x, level x = 0 → ∃ v, core v = x
  level_bound : ∀ x, level x ≤ N
  core_degree : ∀ v, M ≤ host.graph.degree (core v)
  inner_degree : ∀ x, 0 < level x → level x < N → host.graph.degree x = q
  outer_degree : ∀ x, level x = N → host.graph.degree x = 1
  level_step : ∀ x y, host.graph.Adj x y → level x ≤ level y + 1

private def firstLayer (T : Host) (M q : ℕ) : Layered T M q 1 := by
  let p : T.Vertex × Fin M → T.Vertex := Prod.fst
  let S : Host := ⟨T.Vertex ⊕ (T.Vertex × Fin M), inferInstance,
    sprout T.graph p, sprout_tree T.tree p⟩
  let lev : S.Vertex → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  refine ⟨S, sproutCore T.graph p, lev, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    cases x with
    | inl v => exact ⟨v, rfl⟩
    | inr a => exact (by cases hx)
  · intro x; cases x <;> simp [lev]
  · intro v
    have hf : Fintype.card {a : T.Vertex × Fin M // v = a.1} = M := by
      let e : {a : T.Vertex × Fin M // v = a.1} ≃ Fin M := {
        toFun := fun a => a.val.2
        invFun := fun j => ⟨(v, j), rfl⟩
        left_inv := by rintro ⟨⟨w, j⟩, h⟩; dsimp at h; subst w; rfl
        right_inv := fun _ => rfl }
      simpa using Fintype.card_congr e
    change M ≤ (sprout T.graph p).degree (.inl v)
    rw [sprout_degree_core]
    dsimp [p]
    omega
  · intro x hx hx'
    cases x <;> simp [lev] at hx hx'
  · intro x hx
    cases x with
    | inl v => cases hx
    | inr a => exact sprout_degree_leaf T.graph p a
  · intro x y h
    cases x <;> cases y <;> simp [lev]

set_option maxHeartbeats 1200000 in
private def nextLayer {T : Host} {M q N : ℕ} (A : Layered T M q N)
    (hN : 0 < N) (hq : 1 ≤ q) : Layered T M q (N + 1) := by
  let B : Set A.host.Vertex := {x | A.level x = N}
  let p : B × Fin (q - 1) → A.host.Vertex := fun a => a.1.val
  let S : Host := ⟨A.host.Vertex ⊕ (B × Fin (q - 1)), inferInstance,
    sprout A.host.graph p, sprout_tree A.host.tree p⟩
  let lev : S.Vertex → ℕ := Sum.elim A.level (fun _ => N + 1)
  let core : Copy T.graph S.graph := (sproutCore A.host.graph p).comp A.core
  have deg (x : A.host.Vertex) : S.graph.degree (.inl x) =
      A.host.graph.degree x + if A.level x = N then q - 1 else 0 := by
    rw [sprout_degree_core]
    rw [← Nat.card_eq_fintype_card]
    simpa only [p, B, Set.mem_setOf_eq] using
      congrArg (A.host.graph.degree x + ·) (selectedFiber_card B (q - 1) x)
  refine ⟨S, core, lev, A.core_level, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    cases x with
    | inl v =>
      obtain ⟨w, hw⟩ := A.zero_core v hx
      exact ⟨w, congrArg Sum.inl hw⟩
    | inr a => dsimp [lev] at hx; omega
  · intro x
    cases x with
    | inl v => exact (A.level_bound v).trans (by omega)
    | inr a => exact le_rfl
  · intro v
    change M ≤ S.graph.degree (.inl (A.core v))
    rw [deg, A.core_level, if_neg (by omega), Nat.add_zero]
    exact A.core_degree v
  · intro x hx hx'
    cases x with
    | inl v =>
      change 0 < A.level v at hx
      change A.level v < N + 1 at hx'
      rw [deg]
      by_cases hv : A.level v = N
      · rw [if_pos hv, A.outer_degree v hv]
        omega
      · rw [if_neg hv, Nat.add_zero, A.inner_degree v hx (by omega)]
    | inr a => dsimp [lev] at hx'; omega
  · intro x hx
    cases x with
    | inl v =>
      change A.level v = N + 1 at hx
      have := A.level_bound v
      omega
    | inr a => exact sprout_degree_leaf A.host.graph p a
  · intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact A.level_step v w h
      | inr a =>
        change v = a.1.val at h
        subst v
        dsimp [lev]
        have := a.1.property
        dsimp [B] at this
        omega
    | inr a =>
      cases y with
      | inl v =>
        change v = a.1.val at h
        subst v
        dsimp [lev]
        have := a.1.property
        dsimp [B] at this
        omega
      | inr b => exact h.elim

/-- An arbitrary finite tree embeds as the core; every nonleaf branch vertex
has degree `q`, and all leaves have the prescribed finite depth. -/
def layeredHost (T : Host) (M q n : ℕ) (hq : 1 ≤ q) : Layered T M q (n + 1) := by
  induction n with
  | zero => exact firstLayer T M q
  | succ n ih => exact nextLayer ih (by omega) hq

private theorem walk_level_bound {W : Type} {G : SimpleGraph W} (level : W → ℕ)
    (step : ∀ x y, G.Adj x y → level x ≤ level y + 1)
    {x y : W} (p : G.Walk x y) : level y ≤ level x + p.length := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have hs := step y x h.symm
    simp only [Walk.length_cons]
    omega

/-- Every copy of a higher-maximum-degree tree meets the original core and
lies strictly less than its order away from it in layer coordinates. -/
theorem copy_level_bound {V : Type} [Fintype V] {H : SimpleGraph V} (hH : H.IsTree)
    {T : Host} {M q N : ℕ} (A : Layered T M q N) (hq : 1 ≤ q)
    (hdegree : q < H.maxDegree) (c : Copy H A.host.graph) :
    ∃ v : V, A.level (c v) = 0 ∧ ∀ w, A.level (c w) < Fintype.card V := by
  haveI : Nonempty V := hH.connected.nonempty
  obtain ⟨v, hv⟩ := H.exists_maximal_degree_vertex
  have hzero : A.level (c v) = 0 := by
    by_contra hn
    have hb := A.level_bound (c v)
    have hd := c.degree_le v
    by_cases houter : A.level (c v) = N
    · rw [A.outer_degree _ houter] at hd
      omega
    · rw [A.inner_degree _ (by omega) (by omega)] at hd
      omega
  refine ⟨v, hzero, ?_⟩
  intro w
  obtain ⟨p, hp, _⟩ := hH.existsUnique_path v w
  have hb := walk_level_bound A.level A.level_step (p.map c.toHom)
  have hl : p.length < Fintype.card V := hp.length_lt
  change A.level (c w) ≤ A.level (c v) + (p.map c.toHom).length at hb
  simp only [Walk.length_map, hzero, Nat.zero_add] at hb
  omega

/-- The degree hypothesis supplies a finite supertree of every initial tree.
Every copy has its full root degree budget, and no leaf is within `l` further
layers of any copy vertex. This statement does not assume any arm paths. -/
theorem exists_buffered_host {V : Type} [Fintype V] {H : SimpleGraph V}
    (hH : H.IsTree) (m : V → ℕ) (l : ℕ)
    (hdegree : (∑ v, m v) + 2 < H.maxDegree) (T : Host) :
    ∃ (q M : ℕ) (A : Layered T M q (Fintype.card V + l + 1)),
      2 ≤ q ∧ q ≤ (∑ v, m v) + 2 ∧ q < H.maxDegree ∧ 2 ≤ M ∧
      (∀ c : Copy H A.host.graph, ∀ v, A.level (c v) < Fintype.card V) ∧
      (∀ c : Copy H A.host.graph, ∀ v, H.degree v + m v ≤ A.host.graph.degree (c v)) ∧
      (∀ x, A.level x < Fintype.card V + l + 1 → 2 ≤ A.host.graph.degree x) := by
  obtain ⟨q, hq, hqk, hsafe⟩ := exists_safe_degree (fun v => H.degree v) m
  let M := H.maxDegree + (∑ v, m v) + 2
  let A := layeredHost T M q (Fintype.card V + l) (by omega)
  have hqdegree : q < H.maxDegree := by omega
  have hc (c : Copy H A.host.graph) (v : V) : A.level (c v) < Fintype.card V := by
    obtain ⟨_, _, hb⟩ := copy_level_bound hH A (by omega) hqdegree c
    exact hb v
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hm (v : V) : m v ≤ ∑ w, m w :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  refine ⟨q, M, A, hq, hqk, hqdegree, hM, hc, ?_, ?_⟩
  · intro c v
    have hb := hc c v
    by_cases hzero : A.level (c v) = 0
    · obtain ⟨w, hw⟩ := A.zero_core _ hzero
      have hd := A.core_degree w
      rw [hw] at hd
      have hv := H.degree_le_maxDegree v
      have hmv := hm v
      dsimp [M] at hd
      omega
    · have hi : A.level (c v) < Fintype.card V + l + 1 := by omega
      have he := A.inner_degree _ (by omega) hi
      rw [he]
      apply hsafe v
      have hcd := c.degree_le v
      rw [he] at hcd
      exact hcd
  · intro x hx
    by_cases hzero : A.level x = 0
    · obtain ⟨v, hv⟩ := A.zero_core x hzero
      have hd := A.core_degree v
      rw [hv] at hd
      omega
    · rw [A.inner_degree x (by omega) hx]
      exact hq

private theorem copy_reflects {V W : Type} {P : SimpleGraph V} {G : SimpleGraph W}
    (hP : P.Connected) (hG : G.IsAcyclic) (c : Copy P G) {v w : V}
    (h : G.Adj (c v) (c w)) : P.Adj v w := by
  obtain ⟨p, hp⟩ := hP.exists_isPath v w
  have hmap : (p.map c.toHom).IsPath := hp.map c.injective
  have he := (hG.subsingleton_path (c v) (c w)).elim
    (⟨p.map c.toHom, hmap⟩ : G.Path (c v) (c w)) (Path.singleton h)
  have hl := congrArg (fun r : G.Path (c v) (c w) => r.val.length) he
  exact Walk.adj_of_length_eq_one (by simpa using hl)

private theorem exterior_attachment_unique {V W : Type} {P : SimpleGraph V}
    {G : SimpleGraph W} (hP : P.Connected) (hG : G.IsAcyclic) (c : Copy P G)
    {v w : V} {y : W} (hy : y ∉ Set.range c)
    (hv : G.Adj (c v) y) (hw : G.Adj (c w) y) : v = w := by
  obtain ⟨p, hp⟩ := hP.exists_isPath v w
  have hmap : (p.map c.toHom).IsPath := hp.map c.injective
  have hy' : y ∉ (p.map c.toHom).support := by
    simp only [Walk.support_map, List.mem_map]
    rintro ⟨z, _, hz⟩
    exact hy ⟨z, hz⟩
  have hr : (Walk.cons hv.symm (p.map c.toHom)).IsPath := hmap.cons hy'
  have he := hG.eq_snd_of_adj_start hr hw.symm
    (Walk.end_mem_support (Walk.cons hv.symm (p.map c.toHom)))
  exact c.injective (by simpa using he.symm)

private def externalNeighbors {V W : Type} [Fintype W] {P : SimpleGraph V}
    [Fintype V] {G : SimpleGraph W} (c : Copy P G) (v : V) : Finset W :=
  G.neighborFinset (c v) \ Finset.univ.image c

/-- A tree copy can acquire an arbitrary prescribed finite family of new leaves
when every parent has enough unused degree. The chosen leaves are jointly fresh. -/
theorem sprout_copy {V W L : Type} [Fintype V] [Fintype W] [Fintype L]
    {P : SimpleGraph V} {G : SimpleGraph W} (hP : P.IsTree) (hG : G.IsTree)
    (c : Copy P G) (p : L → V)
    (hbudget : ∀ v, P.degree v + Fintype.card {a : L // v = p a} ≤ G.degree (c v)) :
    ∃ e : Copy (sprout P p) G, ∀ v, e (.inl v) = c v := by
  have hcard (v : V) : Fintype.card {a : L // v = p a} ≤ (externalNeighbors c v).card := by
    have he : G.neighborFinset (c v) ∩ Finset.univ.image c = (P.neighborFinset v).image c := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
        mem_neighborFinset]
      constructor
      · rintro ⟨hw, v', rfl⟩
        exact ⟨v', copy_reflects hP.connected hG.isAcyclic c hw, rfl⟩
      · rintro ⟨v', hv', rfl⟩
        exact ⟨c.toHom.map_adj hv', v', rfl⟩
    have hc := Finset.card_sdiff_add_card_inter (G.neighborFinset (c v)) (Finset.univ.image c)
    rw [he, Finset.card_image_of_injective (f := (c : V → W)) _ c.injective,
      card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
    have hb := hbudget v
    change (G.neighborFinset (c v) \ Finset.univ.image c).card + P.degree v = G.degree (c v) at hc
    dsimp [externalNeighbors]
    omega
  let f (v : V) : {a : L // v = p a} ↪ (externalNeighbors c v) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hcard v))
  let leaf (a : L) : W := (f (p a) ⟨a, rfl⟩).val
  have hadj (a : L) : G.Adj (c (p a)) (leaf a) := by
    have h := (f (p a) ⟨a, rfl⟩).property
    simpa only [mem_neighborFinset] using (Finset.mem_sdiff.mp h).1
  have hfresh (a : L) : leaf a ∉ Set.range c := by
    have h := (f (p a) ⟨a, rfl⟩).property
    rintro ⟨v, hv⟩
    exact (Finset.mem_sdiff.mp h).2 (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩)
  have hchange (a : L) (v : V) (hv : v = p a) : (f v ⟨a, hv⟩).val = leaf a := by
    subst v
    rfl
  have hinj : Function.Injective leaf := by
    intro a b hab
    have hp : p a = p b := exterior_attachment_unique hP.connected hG.isAcyclic c
      (hfresh a) (hadj a) (by rw [hab]; exact hadj b)
    have he : f (p a) ⟨a, rfl⟩ = f (p a) ⟨b, hp⟩ := by
      apply Subtype.ext
      exact hab.trans (hchange b (p a) hp).symm
    exact congrArg Subtype.val ((f (p a)).injective he)
  let e : Copy (sprout P p) G := {
    toHom := {
      toFun := Sum.elim c leaf
      map_rel' := by
        intro x y h
        cases x with
        | inl v =>
          cases y with
          | inl w => exact c.toHom.map_adj h
          | inr a => change v = p a at h; subst v; exact hadj a
        | inr a =>
          cases y with
          | inl v => change v = p a at h; subst v; exact (hadj a).symm
          | inr b => exact h.elim }
    injective' := by
      intro x y h
      cases x with
      | inl v =>
        cases y with
        | inl w => exact congrArg Sum.inl (c.injective h)
        | inr a => exact (hfresh a ⟨v, h⟩).elim
      | inr a =>
        cases y with
        | inl v => exact (hfresh a ⟨v, h.symm⟩).elim
        | inr b => exact congrArg Sum.inr (hinj h) }
  exact ⟨e, fun _ => rfl⟩

private def rootFiberEquiv {V : Type} (m : V → ℕ) (v : V) :
    {a : (Σ w, Fin (m w)) // v = a.1} ≃ Fin (m v) where
  toFun a := a.property.symm ▸ a.val.2
  invFun i := ⟨⟨v, i⟩, rfl⟩
  left_inv := by rintro ⟨⟨w, i⟩, h⟩; dsimp at h; subst w; rfl
  right_inv _ := rfl

private def oneExtensionCopy {V : Type} (H : SimpleGraph V) (m : V → ℕ) :
    Copy (extensionGraph H m 1) (sprout H (fun a : Σ v, Fin (m v) => a.1)) := by
  let f : (Σ v, Fin (m v) × Fin 1) → (Σ v, Fin (m v)) := fun a => ⟨a.1, a.2.1⟩
  let g : (Σ v, Fin (m v)) → (Σ v, Fin (m v) × Fin 1) := fun a => ⟨a.1, (a.2, 0)⟩
  have hleft : Function.LeftInverse g f := by
    rintro ⟨v, i, j⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  refine ⟨⟨Sum.map id f, ?_⟩, Sum.map_injective Function.injective_id hleft.injective⟩
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w => exact h
    | inr a => exact h.1
  | inr a =>
    cases y with
    | inl v => exact h.1
    | inr b =>
      change a.1 = b.1 ∧ a.2.1.val = b.2.1.val ∧
        (a.2.2.val + 1 = b.2.2.val ∨ b.2.2.val + 1 = a.2.2.val) at h
      have ha := a.2.2.isLt
      have hb := b.2.2.isLt
      omega

/-- The first arm edge can be supplied for all roots simultaneously from the
degree budgets; no disjointness or already existing extension is assumed. -/
theorem hasExtension_one {V : Type} [Fintype V] {H : SimpleGraph V} (hH : H.IsTree)
    (m : V → ℕ) {G : Host} (c : Copy H G.graph)
    (hbudget : ∀ v, H.degree v + m v ≤ G.graph.degree (c v)) : HasExtension m 1 c := by
  have hf (v : V) : Fintype.card {a : (Σ w, Fin (m w)) // v = a.1} = m v := by
    simpa using Fintype.card_congr (rootFiberEquiv m v)
  obtain ⟨e, he⟩ := sprout_copy hH G.tree c (fun a : Σ v, Fin (m v) => a.1) (by
    intro v
    rw [hf]
    exact hbudget v)
  refine ⟨e.comp (oneExtensionCopy H m), ?_⟩
  intro v
  exact he v

end
end D5.S3.Combinatorics.Graph.Walks.AmoebaConfinement
