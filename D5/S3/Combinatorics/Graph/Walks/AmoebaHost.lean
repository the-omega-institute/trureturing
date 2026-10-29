/- GID: D5/S3/Combinatorics/Graph/Walks/AmoebaHost
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/AmoebaHost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Finite layered trees with a preserved core and controlled branching degrees. -/

/-
   copy_level_bound: proof_shape: content; escape_witness: the unique-path level
   bound placing every copy vertex within the finite core radius; consumers:
   exists_buffered_host.
   exists_buffered_host: proof_shape: content; escape_witness: the explicit
   finite layered host construction with core budgets, safe degree and depth;
   consumers: hasExtension_of_buffer, total_confinement.
   sprout_copy: proof_shape: content; escape_witness: the jointly injective
   fresh-leaf selection over all parent fibers; consumers: hasExtension_one.
   hasExtension_one: proof_shape: content; escape_witness: the explicit
   simultaneous length-one extension embedding; consumers: hasExtension_of_buffer.
   hasExtension_of_buffer: proof_shape: content; escape_witness: the finite
   nonbacktracking continuation of every arm with joint injectivity; consumers:
   total_confinement.
   total_confinement: proof_shape: content; escape_witness: the all-copy,
   arbitrary-initial-host composition of buffered extension and deadness;
   consumers: none.
   admission_basis: open-problem-resolution (#23364; Proved)
   Direct frozen dependencies: none (same-delivery AmoebaConfinement and pinned Mathlib).
-/

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
  refine ⟨⟨Sum.map id f, ?_⟩, Sum.map_injective.mpr ⟨Function.injective_id, hleft.injective⟩⟩
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

private theorem neighbor_other {W : Type} [Fintype W] {G : SimpleGraph W}
    (v previous : W) (hv : 2 ≤ G.degree v) : ∃ w, G.Adj v w ∧ w ≠ previous := by
  by_contra h
  push_neg at h
  have hs : (G.neighborSet v).Subsingleton := by
    intro a ha b hb
    exact (h a ha).trans (h b hb).symm
  have hc : G.degree v ≤ 1 := by
    rw [← ncard_neighborSet]
    exact Set.ncard_le_one_iff_subsingleton.mpr hs
  omega

private theorem prolong_path {W : Type} [Fintype W] {G : SimpleGraph W}
    (hG : G.IsTree) (level : W → ℕ) (N : ℕ)
    (hstep : ∀ x y, G.Adj x y → level x ≤ level y + 1)
    (hinterior : ∀ x, level x < N → 2 ≤ G.degree x)
    {a b : W} (p : G.Walk a b) (hp : p.IsPath) (hpos : 0 < p.length) (n : ℕ)
    (hbuffer : level a + p.length + n < N) :
    ∃ z, ∃ q : G.Walk a z, q.IsPath ∧ q.length = p.length + n ∧ q.snd = p.snd := by
  induction n generalizing b p with
  | zero => exact ⟨b, p, hp, by simp, rfl⟩
  | succ n ih =>
    have hl := walk_level_bound level hstep p
    obtain ⟨y, hy, hne⟩ := neighbor_other b p.penultimate (hinterior b (by omega))
    have hpath : (p.concat hy).IsPath := hp.concat (by
      intro hymem
      exact hne (hG.isAcyclic.eq_penultimate_of_adj_end hp hy hymem)) hy
    have hsnd : (p.concat hy).snd = p.snd := by
      cases p with
      | nil => simp at hpos
      | cons h p => simp [Walk.concat_cons, Walk.snd]
    obtain ⟨z, q, hq, hlen, hs⟩ := ih (p.concat hy) hpath
      (by simp only [Walk.length_concat]; omega)
      (by simp only [Walk.length_concat]; omega)
    refine ⟨z, q, hq, ?_, hs.trans hsnd⟩
    simp only [Walk.length_concat] at hlen
    omega

private theorem path_tail_outside {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (hH : H.Connected) (hG : G.IsAcyclic) (c : Copy H G)
    {v : V} {z : W} (p : G.Walk (c v) z) (hp : p.IsPath)
    (hfirst : p.snd ∉ Set.range c) : ∀ y ∈ p.support.tail, y ∉ Set.range c := by
  rintro y hy ⟨w, rfl⟩
  have hne : c w ≠ c v := by
    intro he
    cases p with
    | nil => simp at hy
    | cons h p =>
      exact (List.nodup_cons.mp hp.support_nodup).1 (he ▸ hy)
  have hym : c w ∈ p.support := List.mem_of_mem_tail hy
  obtain ⟨s, hs⟩ := hH.exists_isPath v w
  have he := (hG.subsingleton_path (c v) (c w)).elim
    (⟨p.takeUntil (c w) hym, hp.takeUntil hym⟩ : G.Path (c v) (c w))
    ⟨s.map c.toHom, hs.map c.injective⟩
  have he' := congrArg (fun r : G.Path (c v) (c w) => r.val.snd) he
  rw [Walk.snd_takeUntil hne] at he'
  have hsnd : (s.map c.toHom).snd = c s.snd := by cases s <;> simp [Walk.snd]
  exact hfirst ⟨s.snd, hsnd.symm.trans he'.symm⟩

private theorem paths_meet_only_same_arm {V W : Type} {H : SimpleGraph V}
    {G : SimpleGraph W} (hH : H.Connected) (hG : G.IsAcyclic) (c : Copy H G)
    {v w : V} {x y z : W} (p : G.Walk (c v) x) (q : G.Walk (c w) y)
    (hp : p.IsPath) (hq : q.IsPath) (hfp : p.snd ∉ Set.range c)
    (hfq : q.snd ∉ Set.range c) (hzp : z ∈ p.support.tail) (hzq : z ∈ q.support.tail) :
    v = w ∧ p.snd = q.snd := by
  have hout := path_tail_outside hH hG c p hp hfp z hzp
  have hzp' := List.mem_of_mem_tail hzp
  have hzq' := List.mem_of_mem_tail hzq
  have hzne v : z ≠ c v := fun h => hout ⟨v, h.symm⟩
  have hps := Walk.snd_takeUntil (hzne v) p hzp'
  have hqs := Walk.snd_takeUntil (hzne w) q hzq'
  by_cases hvw : v = w
  · subst w
    have he := (hG.subsingleton_path (c v) z).elim
      (⟨p.takeUntil z hzp', hp.takeUntil hzp'⟩ : G.Path (c v) z)
      ⟨q.takeUntil z hzq', hq.takeUntil hzq'⟩
    refine ⟨rfl, ?_⟩
    have hh := congrArg (fun r : G.Path (c v) z => r.val.snd) he
    simpa only [hps, hqs] using hh
  · obtain ⟨s, hs⟩ := hH.exists_isPath v w
    let r := q.takeUntil z hzq'
    have hr : r.IsPath := hq.takeUntil hzq'
    have hrf : r.snd ∉ Set.range c := by simpa only [r, hqs] using hfq
    have hdis : (s.map c.toHom).support.Disjoint r.support.tail := by
      intro u hu hur
      have hu' : u ∈ Set.range c := by
        simp only [Walk.support_map, List.mem_map] at hu
        obtain ⟨a, _, ha⟩ := hu
        exact ⟨a, ha⟩
      exact path_tail_outside hH hG c r hr hrf u hur hu'
    have hpath : ((s.map c.toHom).append r).IsPath :=
      (Walk.isPath_append _ _).mpr ⟨hs.map c.injective, hr.tail, hdis⟩
    have he := (hG.subsingleton_path (c v) z).elim
      (⟨p.takeUntil z hzp', hp.takeUntil hzp'⟩ : G.Path (c v) z)
      ⟨(s.map c.toHom).append r, hpath⟩
    have hh := congrArg (fun t : G.Path (c v) z => t.val.snd) he
    rw [hps] at hh
    cases s with
    | nil => exact (hvw rfl).elim
    | @cons a b d h s =>
      exact (hfp ⟨b, by simpa [Walk.snd] using hh.symm⟩).elim

/-- Root degree budgets and a leaf-free layer buffer realize every arm of any
finite length simultaneously, with all off-copy vertices jointly distinct. -/
theorem hasExtension_of_buffer {V : Type} [Fintype V] {H : SimpleGraph V}
    (hH : H.IsTree) (m : V → ℕ) (l : ℕ) {G : Host} (c : Copy H G.graph)
    (level : G.Vertex → ℕ) (N : ℕ)
    (hstep : ∀ x y, G.graph.Adj x y → level x ≤ level y + 1)
    (hinterior : ∀ x, level x < N → 2 ≤ G.graph.degree x)
    (hbudget : ∀ v, H.degree v + m v ≤ G.graph.degree (c v))
    (hmargin : ∀ v, level (c v) + l < N) : HasExtension m l c := by
  cases l with
  | zero =>
    let e : Copy (extensionGraph H m 0) G.graph := {
      toHom := {
        toFun := Sum.elim c (fun a => Fin.elim0 a.2.2)
        map_rel' := by
          intro x y h
          cases x with
          | inl v =>
            cases y with
            | inl w => exact c.toHom.map_adj h
            | inr a => exact Fin.elim0 a.2.2
          | inr a => exact Fin.elim0 a.2.2 }
      injective' := by
        intro x y h
        cases x with
        | inl v =>
          cases y with
          | inl w => exact congrArg Sum.inl (c.injective h)
          | inr a => exact Fin.elim0 a.2.2
        | inr a => exact Fin.elim0 a.2.2 }
    exact ⟨e, fun _ => rfl⟩
  | succ n =>
    obtain ⟨e, he⟩ := hasExtension_one hH m c hbudget
    let R := Σ v, Fin (m v)
    let first (a : R) := e (.inr ⟨a.1, (a.2, 0)⟩)
    have hfirstadj (a : R) : G.graph.Adj (c a.1) (first a) := by
      rw [← he]
      exact e.toHom.map_adj (show (extensionGraph H m 1).Adj (.inl a.1) (.inr ⟨a.1, (a.2, 0)⟩) from ⟨rfl, rfl⟩)
    have hfirstout (a : R) : first a ∉ Set.range c := by
      rintro ⟨v, hv⟩
      have hh := e.injective ((he v).trans hv)
      cases hh
    have hfirstinj : Function.Injective first := by
      intro a b hab
      have hh := Sum.inr.inj (e.injective hab)
      exact congrArg (fun t : Σ v, Fin (m v) × Fin 1 => (⟨t.1, t.2.1⟩ : R)) hh
    have hex (a : R) : ∃ z, ∃ p : G.graph.Walk (c a.1) z,
        p.IsPath ∧ p.length = n + 1 ∧ p.snd = first a := by
      obtain ⟨z, p, hp, hl, hs⟩ := prolong_path G.tree level N hstep hinterior
        (hfirstadj a).toWalk (Walk.IsPath.of_adj (hfirstadj a)) (by simp) n (by
          have hm := hmargin a.1
          simp only [Adj.toWalk, Walk.length_cons, Walk.length_nil]
          omega)
      exact ⟨z, p, hp, by simpa [Nat.add_comm] using hl, hs⟩
    choose endpoint path hpath hlen hsnd using hex
    have htail (a : R) (j : ℕ) : (path a).getVert (j + 1) ∈ (path a).support.tail := by
      apply Walk.getVert_mem_tail_support
      · rw [Walk.not_nil_iff_lt_length, hlen]
        omega
      · omega
    let f : ExtensionVertex m (n + 1) → G.Vertex := Sum.elim c
      (fun a => (path (⟨a.1, a.2.1⟩ : R)).getVert (a.2.2.val + 1))
    have hout (a : R) (j : ℕ) : (path a).getVert (j + 1) ∉ Set.range c :=
      path_tail_outside hH.connected G.tree.isAcyclic c (path a) (hpath a)
        (by rw [hsnd]; exact hfirstout a) _ (htail a j)
    have hinj : Function.Injective f := by
      intro x y h
      cases x with
      | inl v =>
        cases y with
        | inl w => exact congrArg Sum.inl (c.injective h)
        | inr b => exact (hout ⟨b.1, b.2.1⟩ b.2.2.val ⟨v, h⟩).elim
      | inr a =>
        cases y with
        | inl w => exact (hout ⟨a.1, a.2.1⟩ a.2.2.val ⟨w, h.symm⟩).elim
        | inr b =>
          have hab := paths_meet_only_same_arm hH.connected G.tree.isAcyclic c
            (path (⟨a.1, a.2.1⟩ : R)) (path (⟨b.1, b.2.1⟩ : R))
            (hpath _) (hpath _) (by rw [hsnd]; exact hfirstout _)
            (by rw [hsnd]; exact hfirstout _) (htail _ a.2.2.val)
            (by dsimp [f] at h; rw [h]; exact htail _ b.2.2.val)
          have hr : (⟨a.1, a.2.1⟩ : R) = ⟨b.1, b.2.1⟩ := hfirstinj (by simpa only [hsnd] using hab.2)
          rcases a with ⟨v, i, j⟩
          rcases b with ⟨w, i', j'⟩
          have hv : v = w := congrArg Sigma.fst hr
          subst w
          have hi : i = i' := eq_of_heq (Sigma.mk.inj hr).2
          subst i'
          dsimp [f] at h
          have hj := (hpath (⟨v, i⟩ : R)).getVert_injOn
            (by simp only [Set.mem_setOf_eq, hlen]; omega)
            (by simp only [Set.mem_setOf_eq, hlen]; omega) h
          have hj' : j = j' := Fin.ext (by omega)
          subst j'
          rfl
    refine ⟨⟨⟨f, ?_⟩, hinj⟩, fun _ => rfl⟩
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact c.toHom.map_adj h
      | inr a =>
        rcases h with ⟨rfl, hj⟩
        change G.graph.Adj (c a.1) ((path (⟨a.1, a.2.1⟩ : R)).getVert (a.2.2.val + 1))
        rw [hj]
        exact Walk.adj_snd (by rw [Walk.not_nil_iff_lt_length, hlen]; omega)
    | inr a =>
      cases y with
      | inl v =>
        rcases h with ⟨rfl, hj⟩
        change G.graph.Adj ((path (⟨a.1, a.2.1⟩ : R)).getVert (a.2.2.val + 1)) (c a.1)
        rw [hj]
        exact (Walk.adj_snd (by rw [Walk.not_nil_iff_lt_length, hlen]; omega)).symm
      | inr b =>
        rcases a with ⟨v, i, j⟩
        rcases b with ⟨w, i', j'⟩
        change v = w ∧ i.val = i'.val ∧
          (j.val + 1 = j'.val ∨ j'.val + 1 = j.val) at h
        rcases h with ⟨hv, hi, hj⟩
        subst w
        have hi' : i = i' := Fin.ext hi
        subst i'
        change G.graph.Adj ((path (⟨v, i⟩ : R)).getVert (j.val + 1))
          ((path (⟨v, i⟩ : R)).getVert (j'.val + 1))
        rcases hj with hj | hj
        · have ha := (path (⟨v, i⟩ : R)).adj_getVert_succ (i := j.val + 1)
            (by rw [hlen]; omega)
          simpa only [show j.val + 1 + 1 = j'.val + 1 by omega] using ha
        · apply Adj.symm
          have ha := (path (⟨v, i⟩ : R)).adj_getVert_succ (i := j'.val + 1)
            (by rw [hlen]; omega)
          simpa only [show j'.val + 1 + 1 = j.val + 1 by omega] using ha

/-- Gurvich–Krnc–Vyalyi ordinary-amoeba Conjecture 1 in its finite tree domain. -/
theorem total_confinement : conjecture := by
  intro V _ H hH m l hdegree T hcopy
  obtain ⟨q, M, A, _, _, _, _, hlevel, hbudget, hinterior⟩ :=
    exists_buffered_host hH m l hdegree T
  refine ⟨A.host, ⟨A.core⟩, ?_, ?_⟩
  · obtain ⟨c⟩ := hcopy
    exact ⟨A.core.comp c⟩
  · intro c
    apply dead_of_hasExtension m l c
    apply hasExtension_of_buffer hH m l c A.level (Fintype.card V + l + 1)
      A.level_step hinterior (hbudget c)
    intro v
    have := hlevel c v
    omega

end
end D5.S3.Combinatorics.Graph.Walks.AmoebaConfinement
