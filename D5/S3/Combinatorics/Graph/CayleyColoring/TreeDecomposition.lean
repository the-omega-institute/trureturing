/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Deleting a pivot expresses a native tree as independently rooted attached branches. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The fixed-root, order-dual Seitz construction on native simple graphs. -/

namespace CayleyProbe

open SimpleGraph

universe u

abbrev Tree (V : Type u) := {G : SimpleGraph V // G.IsTree}

variable {V : Type u}

def Peak [LT V] (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w, G.Adj v w → w < v

def RootedLeaf (G : SimpleGraph V) (r v : V) : Prop :=
  ¬ ∃ w, G.Adj v w ∧ G.dist r v < G.dist r w

noncomputable def filterCard [Fintype V] (p : V → Prop) : Nat := by
  classical
  exact (Finset.univ.filter p).card

def cut (G : SimpleGraph V) (p : V) : SimpleGraph V where
  Adj x y := x ≠ p ∧ y ≠ p ∧ G.Adj x y
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.2.2.ne rfl⟩

private theorem cut_le (G : SimpleGraph V) (p : V) : cut G p ≤ G :=
  fun _ _ h ↦ h.2.2

private def cutWalk {G : SimpleGraph V} {p x y : V} (w : G.Walk x y)
    (h : p ∉ w.support) : (cut G p).Walk x y :=
  w.transfer _ fun e he ↦ by
    obtain ⟨a, b⟩ := e
    exact ⟨fun ha ↦ h (ha ▸ w.fst_mem_support_of_mem_edges he),
      fun hb ↦ h (hb ▸ w.snd_mem_support_of_mem_edges he), w.edges_subset_edgeSet he⟩

private theorem cut_reachable_ne {G : SimpleGraph V} {p x y : V} (hx : x ≠ p)
    (h : (cut G p).Reachable x y) : y ≠ p := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | cons ha w ih => exact ih ha.2.1

private theorem existsUnique_attachment {G : SimpleGraph V} (hG : G.IsTree)
    {p x : V} (hx : x ≠ p) :
    ∃! y, G.Adj p y ∧ (cut G p).Reachable y x := by
  classical
  obtain ⟨w, hw, _⟩ := hG.connected.exists_path_of_dist p x
  cases w with
  | nil => exact (hx rfl).elim
  | @cons _ a _ hp w =>
    obtain ⟨_, hnot⟩ := (Walk.cons_isPath_iff hp w).mp hw
    refine ⟨a, ⟨hp, (cutWalk w hnot).reachable⟩, ?_⟩
    rintro y ⟨hy, hyx⟩
    obtain ⟨q, hq, _⟩ := hyx.exists_path_of_dist
    have hn : p ∉ q.support := by
      intro hm
      have hr := (q.takeUntil p hm).reachable
      exact cut_reachable_ne hy.ne.symm hr rfl
    have hq' : (Walk.cons hy (q.mapLe (cut_le G p))).IsPath :=
      (Walk.cons_isPath_iff _ _).mpr
        ⟨hq.mapLe _, by simpa only [Walk.support_mapLe_eq_support] using hn⟩
    have he := (hG.existsUnique_path p x).unique hq' hw
    simpa using congrArg Walk.snd he

private theorem card_branch_lt [Fintype V] (p : V) (s : Set V) [Fintype s]
    (hp : p ∉ s) : Fintype.card s < Fintype.card V :=
  Fintype.card_subtype_lt hp

theorem shorterNeighbor {G : SimpleGraph V} (hG : G.IsTree)
    {r v : V} (hv : v ≠ r) :
    ∃! w, G.Adj v w ∧ G.dist r w < G.dist r v := by
  obtain ⟨q, hq, hlen⟩ := hG.connected.exists_path_of_dist r v
  have hn := Walk.not_nil_of_ne hv.symm (p := q)
  have hadj := q.adj_penultimate hn
  have hlt : G.dist r q.penultimate < G.dist r v := by
    have hle := G.dist_le q.dropLast
    have hs := q.length_dropLast_add_one hn
    omega
  refine ⟨q.penultimate, ⟨hadj.symm, hlt⟩, ?_⟩
  rintro w ⟨hw, hwlt⟩
  obtain ⟨t, _, ht⟩ := hG.connected.exists_path_of_dist r w
  have hc : (t.concat hw.symm).length = G.dist r v := by
    have hd := hG.dist_eq_dist_add_one_of_adj r hw
    rw [Walk.length_concat, ht]
    omega
  have he := (hG.existsUnique_path r v).unique ((t.concat hw.symm).isPath_of_length_eq_dist hc) hq
  simpa only [Walk.penultimate_concat] using congrArg Walk.penultimate he

theorem tree_of_depth {G : SimpleGraph V} {r : V} (d : V → Nat)
    (zero : ∀ v, d v = 0 ↔ v = r)
    (step : ∀ ⦃v w⦄, G.Adj v w → d v = d w + 1 ∨ d w = d v + 1)
    (parent : ∀ v, v ≠ r → ∃! w, G.Adj v w ∧ d w < d v) :
    G.IsTree ∧ ∀ v, G.dist r v = d v := by
  classical
  have fromRoot (v : V) : ∃ q : G.Walk r v, q.length = d v := by
    induction n : d v using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        have hz := (zero r).mpr rfl
        exact ⟨.nil, by simp_all⟩
      · obtain ⟨w, ⟨ha, hl⟩, _⟩ := parent v hv
        obtain ⟨q, hq⟩ := ih (d w) (n ▸ hl) w rfl
        refine ⟨q.concat ha.symm, ?_⟩
        have hs := step ha
        rw [Walk.length_concat, hq]
        omega
  have walkBound {a b : V} (q : G.Walk a b) : d b ≤ d a + q.length := by
    induction q with
    | nil => simp
    | cons ha q ih =>
      have hs := step ha
      rw [Walk.length_cons]
      omega
  let : Nonempty V := ⟨r⟩
  have conn : G.Connected :=
    ⟨fun x y ↦ (fromRoot x).choose.reachable.symm.trans (fromRoot y).choose.reachable⟩
  refine ⟨⟨conn, ?_⟩, ?_⟩
  · intro v q hq
    obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image q.support.toFinset d
      ⟨v, List.mem_toFinset.mpr q.start_mem_support⟩
    have hx' : x ∈ q.support := List.mem_toFinset.mp hx
    let t := q.rotate x hx'
    have ht : t.IsCycle := hq.rotate hx'
    have hs : ∀ z ∈ t.support, d z ≤ d x := by
      intro z hz
      exact hmax z (List.mem_toFinset.mpr ((Walk.mem_support_rotate_iff q x hx').mp hz))
    have h₁ := t.adj_snd ht.not_nil
    have h₂ := (t.adj_penultimate ht.not_nil).symm
    have h₃ := hs t.snd (List.mem_of_mem_tail (t.snd_mem_tail_support ht.not_nil))
    have h₄ := hs t.penultimate
      (List.mem_of_mem_dropLast (t.penultimate_mem_dropLast_support ht.not_nil))
    have hd₁ := step h₁
    have hd₂ := step h₂
    have hlt₁ : d t.snd < d x := by omega
    have hlt₂ : d t.penultimate < d x := by omega
    have hxr : x ≠ r := fun he ↦ by have := (zero x).mpr he; omega
    exact ht.snd_ne_penultimate ((parent x hxr).unique ⟨h₁, hlt₁⟩ ⟨h₂, hlt₂⟩)
  · intro v
    obtain ⟨q, hq⟩ := fromRoot v
    obtain ⟨t, ht⟩ := conn.exists_walk_length_eq_dist r v
    apply Nat.le_antisymm
    · exact hq ▸ G.dist_le q
    · have hb := walkBound t
      rw [(zero r).mpr rfl, Nat.zero_add, ht] at hb
      exact hb

/-- The blocks and their attachment vertices after deleting the pivot. -/
structure Frame (p : V) where
  parts : Set (Set V)
  cover : ∀ v, v ≠ p ↔ ∃ s ∈ parts, v ∈ s
  separate : ∀ ⦃s t⦄, s ∈ parts → t ∈ parts → ∀ ⦃v⦄, v ∈ s → v ∈ t → s = t
  root : ∀ s : parts, s.val

namespace Frame

variable {p : V} (F : Frame p)

abbrev Branches := ∀ s : F.parts, Tree s.val

private theorem ne_pivot (s : F.parts) {x : V} (hx : x ∈ s.val) : x ≠ p :=
  (F.cover x).mpr ⟨s.val, s.prop, hx⟩

private theorem part_eq {s t : F.parts} {x : V} (hs : x ∈ s.val) (ht : x ∈ t.val) : s = t :=
  Subtype.ext (F.separate s.prop t.prop hs ht)

noncomputable def partAt {x : V} (hx : x ≠ p) : F.parts :=
  ⟨((F.cover x).mp hx).choose, ((F.cover x).mp hx).choose_spec.1⟩

theorem mem_partAt {x : V} (hx : x ≠ p) : x ∈ (F.partAt hx).val :=
  ((F.cover x).mp hx).choose_spec.2

private theorem ext_frame {H : Frame p} (hparts : F.parts = H.parts)
    (hroot : ∀ s hs ht, (F.root ⟨s, hs⟩).val = (H.root ⟨s, ht⟩).val) : F = H := by
  cases F with
  | mk parts cover separate root =>
    cases H with
    | mk parts' cover' separate' root' =>
      dsimp at hparts hroot
      subst parts'
      have hr : root = root' := funext fun s ↦ Subtype.ext (hroot s.val s.prop s.prop)
      subst root'
      rfl

def glue (T : F.Branches) : SimpleGraph V where
  Adj x y :=
    (x = p ∧ ∃ s : F.parts, y = (F.root s).val) ∨
    (y = p ∧ ∃ s : F.parts, x = (F.root s).val) ∨
    ∃ (s : F.parts) (hx : x ∈ s.val) (hy : y ∈ s.val), (T s).val.Adj ⟨x,hx⟩ ⟨y,hy⟩
  symm := ⟨by
    intro x y h
    rcases h with h | h | ⟨s,hx,hy,h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨s, hy, hx, h.symm⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨rfl,s,h⟩ | ⟨rfl,s,h⟩ | ⟨s,hx,hy,h⟩
    · exact F.ne_pivot s (F.root s).prop h.symm
    · exact F.ne_pivot s (F.root s).prop h.symm
    · exact h.ne rfl⟩

variable {F} {T : F.Branches}

private theorem glue_pivot_iff {x : V} :
    (F.glue T).Adj p x ↔ ∃ s : F.parts, x = (F.root s).val := by
  constructor
  · rintro (⟨_, h⟩ | ⟨_, s, hs⟩ | ⟨s, hp, _, _⟩)
    · exact h
    · exact (F.ne_pivot s (F.root s).prop hs.symm).elim
    · exact (F.ne_pivot s hp rfl).elim
  · intro h
    exact Or.inl ⟨rfl,h⟩

private theorem glue_adj_iff_of_mem {s : F.parts} {x y : s.val} :
    (F.glue T).Adj x.val y.val ↔ (T s).val.Adj x y := by
  constructor
  · rintro (⟨h,_⟩ | ⟨h,_⟩ | ⟨t,hx,hy,ha⟩)
    · exact (F.ne_pivot s x.prop h).elim
    · exact (F.ne_pivot s y.prop h).elim
    · have he := F.part_eq hx x.prop
      subst t
      exact ha
  · intro h
    exact Or.inr (Or.inr ⟨s, x.prop, y.prop, h⟩)

private theorem glue_adj_cases {s : F.parts} {x : s.val} {y : V}
    (h : (F.glue T).Adj x.val y) :
    (y = p ∧ x = F.root s) ∨ ∃ hy : y ∈ s.val, (T s).val.Adj x ⟨y,hy⟩ := by
  rcases h with ⟨h,_⟩ | ⟨hp,t,he⟩ | ⟨t,hx,hy,ha⟩
  · exact (F.ne_pivot s x.prop h).elim
  · have ht := F.part_eq x.prop (he.symm ▸ (F.root t).prop)
    subst t
    exact Or.inl ⟨hp, Subtype.ext he⟩
  · have ht := F.part_eq hx x.prop
    subst t
    exact Or.inr ⟨hy,ha⟩

private theorem pivot_adj_of_mem {s : F.parts} {x : s.val} :
    (F.glue T).Adj p x.val ↔ x = F.root s := by
  constructor
  · intro h
    rcases glue_adj_cases h.symm with ⟨_,he⟩ | ⟨hp,_⟩
    · exact he
    · exact (F.ne_pivot s hp rfl).elim
  · rintro rfl
    exact glue_pivot_iff.mpr ⟨s,rfl⟩

noncomputable def depth (T : F.Branches) (x : V) : Nat := by
  classical
  exact if h : x ≠ p then
    (T (F.partAt h)).val.dist (F.root (F.partAt h)) ⟨x, F.mem_partAt h⟩ + 1
  else 0

@[simp] private theorem depth_pivot : depth T p = 0 := by
  simp [depth]

private theorem depth_in {s : F.parts} (x : s.val) :
    depth T x.val = (T s).val.dist (F.root s) x + 1 := by
  rw [depth, dite_eq_left (F.ne_pivot s x.prop)]
  suffices aux : ∀ (t : F.parts) (hx : x.val ∈ t.val), t = s →
      (T t).val.dist (F.root t) ⟨x.val,hx⟩ + 1 = (T s).val.dist (F.root s) x + 1 by
    exact aux _ _ (F.part_eq (F.mem_partAt (F.ne_pivot s x.prop)) x.prop)
  rintro t hx rfl
  rfl

private theorem glue_tree_and_dist (T : F.Branches) :
    (F.glue T).IsTree ∧ ∀ v, (F.glue T).dist p v = depth T v := by
  apply tree_of_depth (depth T)
  · intro v
    by_cases hv : v = p
    · subst v
      simp
    · simp [depth, hv]
  · intro x y ha
    rcases ha with ⟨rfl,s,rfl⟩ | ⟨rfl,s,rfl⟩ | ⟨s,hx,hy,ha⟩
    · right
      rw [depth_pivot, depth_in (F.root s), dist_self]
    · left
      rw [depth_pivot, depth_in (F.root s), dist_self]
    · have hd := (T s).prop.dist_eq_dist_add_one_of_adj (F.root s) ha
      rw [depth_in (T := T) (s := s) ⟨x,hx⟩, depth_in (T := T) (s := s) ⟨y,hy⟩]
      omega
  · intro v hv
    let s := F.partAt hv
    let x : s.val := ⟨v,F.mem_partAt hv⟩
    change ∃! w, (F.glue T).Adj x.val w ∧ depth T w < depth T x.val
    by_cases hx : x = F.root s
    · refine ⟨p, ⟨pivot_adj_of_mem.mpr hx |>.symm, ?_⟩, ?_⟩
      · rw [depth_pivot, depth_in x]
        omega
      · rintro y ⟨ha,hl⟩
        rcases glue_adj_cases (s := s) ha with ⟨he,_⟩ | ⟨hy,_⟩
        · exact he
        · rw [depth_in (T := T) (s := s) ⟨y,hy⟩, depth_in x, hx, dist_self] at hl
          omega
    · obtain ⟨w, ⟨ha,hl⟩, huniq⟩ := shorterNeighbor (T s).prop hx
      refine ⟨w.val, ⟨glue_adj_iff_of_mem.mpr ha, ?_⟩, ?_⟩
      · rw [depth_in w, depth_in x]
        omega
      · rintro y ⟨hay,hly⟩
        rcases glue_adj_cases (s := s) hay with ⟨_,he⟩ | ⟨hy,hay'⟩
        · exact (hx he).elim
        · have hdy := depth_in (T := T) (s := s) ⟨y,hy⟩
          rw [depth_in x, hdy] at hly
          exact congrArg Subtype.val (huniq ⟨y,hy⟩ ⟨hay', by omega⟩)

noncomputable def assemble (T : F.Branches) : Tree V :=
  ⟨F.glue T, (glue_tree_and_dist T).1⟩

private theorem dist_assemble (T : F.Branches) {s : F.parts} (x : s.val) :
    (assemble T).val.dist p x.val = (T s).val.dist (F.root s) x + 1 :=
  ((glue_tree_and_dist T).2 _).trans (depth_in x)

private theorem leaf_assemble (T : F.Branches) {s : F.parts} (x : s.val) :
    RootedLeaf (assemble T).val p x.val ↔ RootedLeaf (T s).val (F.root s) x := by
  unfold RootedLeaf
  constructor
  · rintro h ⟨y,ha,hl⟩
    apply h
    refine ⟨y.val, glue_adj_iff_of_mem.mpr ha, ?_⟩
    rw [dist_assemble T x, dist_assemble T y]
    omega
  · rintro h ⟨y,ha,hl⟩
    rcases glue_adj_cases (T := T) (s := s) ha with ⟨rfl,_⟩ | ⟨hy,ha'⟩
    · simp at hl
    · apply h
      refine ⟨⟨y,hy⟩,ha',?_⟩
      rw [dist_assemble T x, dist_assemble T (s := s) ⟨y,hy⟩] at hl
      omega

end Frame

def cutParts (G : SimpleGraph V) (p : V) : Set (Set V) :=
  {s | ∃ x, x ≠ p ∧ s = ((cut G p).connectedComponentMk x).supp}

private theorem cutParts_ne_pivot {G : SimpleGraph V} {p : V} {s : Set V}
    (hs : s ∈ cutParts G p) {y : V} (hy : y ∈ s) : y ≠ p := by
  obtain ⟨x,hx,rfl⟩ := hs
  exact cut_reachable_ne hx (((cut G p).connectedComponentMk x).reachable_of_mem_supp
    ConnectedComponent.connectedComponentMk_mem hy)

private theorem cutParts_attachment {G : SimpleGraph V} (hG : G.IsTree) {p : V}
    {s : Set V} (hs : s ∈ cutParts G p) :
    ∃! y, G.Adj p y ∧ y ∈ s := by
  obtain ⟨x,hx,rfl⟩ := hs
  simpa only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] using
    existsUnique_attachment hG hx

noncomputable def decomposeFrame (T : Tree V) (p : V) : Frame p where
  parts := cutParts T.val p
  cover := by
    intro x
    constructor
    · intro hx
      exact ⟨_, ⟨x,hx,rfl⟩, ConnectedComponent.connectedComponentMk_mem⟩
    · rintro ⟨s,hs,hx⟩
      exact cutParts_ne_pivot hs hx
  separate := by
    rintro s t ⟨x,_,rfl⟩ ⟨y,_,rfl⟩ v hs ht
    exact congrArg ConnectedComponent.supp (ConnectedComponent.eq_of_common_vertex hs ht)
  root s :=
    let h := (cutParts_attachment T.prop s.prop).exists
    ⟨h.choose,h.choose_spec.2⟩

private theorem decompose_root_adj (T : Tree V) (p : V) (s : (decomposeFrame T p).parts) :
    T.val.Adj p ((decomposeFrame T p).root s).val :=
  (cutParts_attachment T.prop s.prop).exists.choose_spec.1

private theorem cut_induce_eq {G : SimpleGraph V} {p : V} {s : Set V} (hp : p ∉ s) :
    (cut G p).induce s = G.induce s := by
  ext x y
  change (_ ∧ _ ∧ G.Adj x.val y.val) ↔ G.Adj x.val y.val
  simp [show x.val ≠ p from fun h ↦ hp (h ▸ x.prop),
    show y.val ≠ p from fun h ↦ hp (h ▸ y.prop)]

private noncomputable def decomposeBranches (T : Tree V) (p : V) :
    (decomposeFrame T p).Branches := by
  intro s
  refine ⟨T.val.induce s.val, ?_⟩
  rw [← cut_induce_eq ((decomposeFrame T p).ne_pivot s (x := p) · rfl)]
  obtain ⟨x,_,hx⟩ := s.prop
  rw [hx]
  exact (T.prop.isAcyclic.anti (cut_le T.val p)).isTree_connectedComponent _

noncomputable def decompose (p : V) (T : Tree V) : Σ F : Frame p, F.Branches :=
  ⟨decomposeFrame T p, decomposeBranches T p⟩

private theorem assemble_decompose (p : V) (T : Tree V) :
    Frame.assemble (decomposeBranches T p) = T := by
  apply Subtype.ext
  ext x y
  change ((decomposeFrame T p).glue (decomposeBranches T p)).Adj x y ↔ T.val.Adj x y
  constructor
  · rintro (⟨hx,s,hy⟩ | ⟨hy,s,hx⟩ | ⟨s,hx,hy,ha⟩)
    · exact hx.symm ▸ hy.symm ▸ decompose_root_adj T p s
    · exact hx.symm ▸ hy.symm ▸ (decompose_root_adj T p s).symm
    · exact ha
  · intro h
    by_cases hx : x = p
    · subst x
      let F := decomposeFrame T p
      let s := F.partAt h.ne.symm
      have he := (cutParts_attachment T.prop s.prop).unique
        ⟨h, F.mem_partAt h.ne.symm⟩ ⟨decompose_root_adj T p s, (F.root s).prop⟩
      exact Frame.glue_pivot_iff.mpr ⟨s,he⟩
    by_cases hy : y = p
    · subst y
      let F := decomposeFrame T p
      let s := F.partAt h.ne
      have he := (cutParts_attachment T.prop s.prop).unique
        ⟨h.symm, F.mem_partAt h.ne⟩ ⟨decompose_root_adj T p s, (F.root s).prop⟩
      exact (Frame.glue_pivot_iff.mpr ⟨s,he⟩).symm
    · let s : (decomposeFrame T p).parts :=
        ⟨((cut T.val p).connectedComponentMk x).supp, ⟨x,hx,rfl⟩⟩
      have hmem : y ∈ s.val :=
        (ConnectedComponent.mem_supp_congr_adj _ (show (cut T.val p).Adj x y from ⟨hx,hy,h⟩)).mp
          ConnectedComponent.connectedComponentMk_mem
      exact Or.inr (Or.inr ⟨s, ConnectedComponent.connectedComponentMk_mem, hmem, h⟩)

namespace Frame

variable {p : V} {F : Frame p} (T : F.Branches)

private theorem reachable_cut_glue {s : F.parts} {x y : V} (hx : x ∈ s.val) :
    (cut (F.glue T) p).Reachable x y ↔ y ∈ s.val := by
  constructor
  · rintro ⟨q⟩
    induction q with
    | nil => exact hx
    | cons ha q ih =>
      rcases glue_adj_cases (T := T) (x := ⟨_,hx⟩) ha.2.2 with ⟨h,_⟩ | ⟨hz,_⟩
      · exact (ha.2.1 h).elim
      · exact ih hz
  · intro hy
    let f : (T s).val →g cut (F.glue T) p :=
      ⟨Subtype.val, fun {a b} ha ↦ ⟨F.ne_pivot s a.prop, F.ne_pivot s b.prop,
        glue_adj_iff_of_mem.mpr ha⟩⟩
    exact Reachable.map f ((T s).prop.connected ⟨x,hx⟩ ⟨y,hy⟩)

private theorem cut_glue_component {s : F.parts} {x : V} (hx : x ∈ s.val) :
    ((cut (F.glue T) p).connectedComponentMk x).supp = s.val := by
  ext y
  rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun h ↦ (reachable_cut_glue T hx).mp h.symm,
    fun h ↦ ((reachable_cut_glue T hx).mpr h).symm⟩

private theorem decomposeFrame_assemble :
    decomposeFrame (assemble T) p = F := by
  apply (decomposeFrame (assemble T) p).ext_frame
  · ext s
    change s ∈ cutParts (F.glue T) p ↔ s ∈ F.parts
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [cut_glue_component T (F.mem_partAt hx)]
      exact (F.partAt hx).prop
    · intro hs
      let x := F.root ⟨s,hs⟩
      exact ⟨x.val,F.ne_pivot ⟨s,hs⟩ x.prop,(cut_glue_component T x.prop).symm⟩
  · intro s hs ht
    let x := (decomposeFrame (assemble T) p).root ⟨s,hs⟩
    have ha := decompose_root_adj (assemble T) p ⟨s,hs⟩
    exact congrArg Subtype.val
      ((pivot_adj_of_mem (T := T) (s := ⟨s,ht⟩) (x := x)).mp ha)

private theorem branches_heq {H : Frame p} (e : F = H) (U : H.Branches)
    (h : ∀ s hs ht, (T ⟨s,hs⟩).val = (U ⟨s,ht⟩).val) : HEq T U := by
  subst H
  apply heq_of_eq
  funext s
  exact Subtype.ext (h s.val s.prop s.prop)

private theorem decompose_assemble : decompose p (assemble T) = ⟨F,T⟩ := by
  refine Sigma.ext (decomposeFrame_assemble T) ?_
  apply branches_heq _ (decomposeFrame_assemble T)
  intro s hs ht
  ext x y
  exact glue_adj_iff_of_mem (T := T) (s := ⟨s,ht⟩)

end Frame

noncomputable def decomposeEquiv (p : V) : Tree V ≃ (Σ F : Frame p, F.Branches) where
  toFun := decompose p
  invFun := fun a ↦ Frame.assemble a.2
  left_inv := assemble_decompose p
  right_inv := fun a ↦ Frame.decompose_assemble a.2

namespace Frame

variable {p : V} {F : Frame p}

/-- A predicate that excludes the pivot splits across the branch label sets. -/
private noncomputable def splitPredicate (P : V → Prop) (hp : ¬ P p) :
    {x : V // P x} ≃ (Σ s : F.parts, {x : s.val // P x.val}) where
  toFun x :=
    let hx : x.val ≠ p := fun he ↦ hp (he ▸ x.prop)
    ⟨F.partAt hx, ⟨⟨x.val,F.mem_partAt hx⟩,x.prop⟩⟩
  invFun a := ⟨a.2.val.val,a.2.prop⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨s,x⟩
    let hx : x.val.val ≠ p := fun he ↦ hp (he ▸ x.prop)
    change (⟨F.partAt hx, ⟨⟨x.val.val,F.mem_partAt hx⟩,x.prop⟩⟩ : Σ s : F.parts,
      {x : s.val // P x.val}) = ⟨s,x⟩
    suffices aux : ∀ (t : F.parts) (ht : x.val.val ∈ t.val), t = s →
        (⟨t, ⟨⟨x.val.val,ht⟩,x.prop⟩⟩ : Σ s : F.parts, {x : s.val // P x.val}) = ⟨s,x⟩ by
      exact aux _ _ (F.part_eq (F.mem_partAt hx) x.val.prop)
    rintro t ht rfl
    rfl

private theorem natCard_branch_lt [Finite V] (s : F.parts) :
    Nat.card s.val < Nat.card V := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite s.val
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact card_branch_lt p s.val (fun hp ↦ F.ne_pivot s hp rfl)

end Frame

private theorem peak_decompose [LinearOrder V] (p : V) (hmin : ∀ w, p ≤ w)
    (T : Tree V) {s : (decomposeFrame T p).parts} (x : s.val) :
    Peak T.val x.val ↔ Peak (decomposeBranches T p s).val x := by
  constructor
  · intro h y ha
    exact h y.val ha
  · intro h y ha
    have hg : (Frame.assemble (decomposeBranches T p)).val.Adj x.val y := by
      rw [assemble_decompose]
      exact ha
    rcases Frame.glue_adj_cases (s := s) hg with ⟨he,_⟩ | ⟨hy,ha'⟩
    · rw [he]
      exact lt_of_le_of_ne (hmin x.val) (((decomposeFrame T p).ne_pivot s x.prop).symm)
    · exact h ⟨y,hy⟩ ha'

private theorem iso_dist {G H : SimpleGraph V} (e : G ≃g H) (hG : G.Connected)
    (hH : H.Connected) (x y : V) :
    H.dist (e x) (e y) = G.dist x y := by
  apply Nat.le_antisymm
  · obtain ⟨q,h⟩ := hG.exists_walk_length_eq_dist x y
    simpa [h] using H.dist_le (q.map e.toHom)
  · obtain ⟨q,h⟩ := hH.exists_walk_length_eq_dist (e x) (e y)
    simpa [h] using G.dist_le (q.map e.symm.toHom)

private theorem iso_leaf_iff {G H : SimpleGraph V} (e : G ≃g H) (hG : G.Connected)
    (hH : H.Connected) (r x : V) :
    RootedLeaf H (e r) (e x) ↔ RootedLeaf G r x := by
  unfold RootedLeaf
  apply not_congr
  constructor
  · rintro ⟨y,ha,hd⟩
    obtain ⟨w,rfl⟩ := e.toEquiv.surjective y
    change H.Adj (e x) (e w) at ha
    change H.dist (e r) (e x) < H.dist (e r) (e w) at hd
    refine ⟨w,e.map_adj_iff.mp ha,?_⟩
    simpa only [iso_dist e hG hH] using hd
  · rintro ⟨y,ha,hd⟩
    exact ⟨e y,e.map_adj_iff.mpr ha,by simpa only [iso_dist e hG hH]⟩

def relabelTree (e : V ≃ V) (T : Tree V) : Tree V :=
  ⟨T.val.comap e.symm, (Iso.comap e.symm T.val).isTree_iff.mpr T.prop⟩

def relabelEquiv (e : V ≃ V) : Tree V ≃ Tree V where
  toFun := relabelTree e
  invFun := relabelTree e.symm
  left_inv := by
    intro T
    apply Subtype.ext
    ext x y
    change T.val.Adj (e.symm (e x)) (e.symm (e y)) ↔ T.val.Adj x y
    simp
  right_inv := by
    intro T
    apply Subtype.ext
    ext x y
    change T.val.Adj (e (e.symm x)) (e (e.symm y)) ↔ T.val.Adj x y
    simp

private theorem relabel_leaf_card (e : V ≃ V) (T : Tree V) (r : V) :
    Nat.card {x // RootedLeaf T.val r x} =
    Nat.card {x // RootedLeaf (relabelTree e T).val (e r) x} := by
  let i := (Iso.comap e.symm T.val).symm
  have he (x : V) : i x = e x := rfl
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro x
  have h := (iso_leaf_iff i T.prop.connected (relabelTree e T).prop.connected r x).symm
  change RootedLeaf T.val r x ↔ RootedLeaf (T.val.comap e.symm) (e r) (e x)
  simpa only [he] using h

private theorem not_leaf_pivot [Nontrivial V] (T : Tree V) (p : V) : ¬ RootedLeaf T.val p p := by
  obtain ⟨y,hy⟩ := T.prop.connected.preconnected.exists_adj_of_nontrivial p
  intro h
  apply h
  refine ⟨y,hy,?_⟩
  rw [dist_self, dist_eq_one_iff_adj.mpr hy]
  omega

private theorem not_peak_min [Nontrivial V] [LinearOrder V] (T : Tree V) (p : V)
    (hmin : ∀ w, p ≤ w) : ¬ Peak T.val p := by
  obtain ⟨y,hy⟩ := T.prop.connected.preconnected.exists_adj_of_nontrivial p
  exact fun h ↦ (not_lt_of_ge (hmin y)) (h y hy)

private theorem count_step [Finite V] [Nontrivial V] [LinearOrder V] (p : V) (hmin : ∀ w, p ≤ w)
    (T : Tree V) (U : (decomposeFrame T p).Branches)
    (hbranch : ∀ s : (decomposeFrame T p).parts,
      Nat.card {x // Peak (decomposeBranches T p s).val x} =
      Nat.card {x // RootedLeaf (U s).val ((decomposeFrame T p).root s) x}) :
    Nat.card {x // Peak T.val x} = Nat.card {x // RootedLeaf (Frame.assemble U).val p x} := by
  let F := decomposeFrame T p
  let e₁ := F.splitPredicate (Peak T.val) (not_peak_min T p hmin)
  let e₂ := F.splitPredicate (RootedLeaf (Frame.assemble U).val p)
    (not_leaf_pivot (Frame.assemble U) p)
  have equivalence (s : F.parts) :
      {x : s.val // Peak T.val x.val} ≃ {x : s.val // RootedLeaf (Frame.assemble U).val p x.val} := by
    let P := {x // Peak (decomposeBranches T p s).val x}
    let L := {x // RootedLeaf (U s).val (F.root s) x}
    letI : Fintype P := Fintype.ofFinite P
    letI : Fintype L := Fintype.ofFinite L
    have h : Fintype.card P = Fintype.card L := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hbranch s
    exact (Equiv.subtypeEquivRight (peak_decompose p hmin T)).trans
      ((Fintype.equivOfCardEq h).trans (Equiv.subtypeEquivRight (Frame.leaf_assemble U)).symm)
  exact Nat.card_congr (e₁.trans ((Equiv.sigmaCongrRight equivalence).trans e₂.symm))

/-- The recursion acts over all finite label types in one universe. -/
private noncomputable def fixedRootEquivSized (n : Nat) :
    ∀ (W : Type u) [Finite W] [LinearOrder W] (r : W), Nat.card W = n →
      {e : Tree W ≃ Tree W //
        ∀ T, Nat.card {x // Peak T.val x} = Nat.card {x // RootedLeaf (e T).val r x}} := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W _ _ r hn
    by_cases hW : Nontrivial W
    · letI := hW
      letI : Fintype W := Fintype.ofFinite W
      let p := (Finset.univ : Finset W).min' ⟨r,Finset.mem_univ r⟩
      have hmin (x : W) : p ≤ x := Finset.min'_le _ _ (Finset.mem_univ x)
      let branchEquiv (F : Frame p) (s : F.parts) :=
        ih (Nat.card s.val) (hn ▸ F.natCard_branch_lt s) s.val (F.root s) rfl
      let changeBranches : Equiv.Perm (Σ F : Frame p, F.Branches) :=
        Equiv.sigmaCongrRight fun F ↦ Equiv.piCongrRight fun s ↦ (branchEquiv F s).val
      let changeAtPivot := (decomposeEquiv p).trans (changeBranches.trans (decomposeEquiv p).symm)
      let swap := Equiv.swap p r
      refine ⟨changeAtPivot.trans (relabelEquiv swap), ?_⟩
      intro T
      let F := decomposeFrame T p
      let U : F.Branches := fun s ↦ (branchEquiv F s).val (decomposeBranches T p s)
      have hstep := count_step p hmin T U (fun s ↦ (branchEquiv F s).prop _)
      apply hstep.trans
      change Nat.card {x // RootedLeaf (Frame.assemble U).val p x} =
        Nat.card {x // RootedLeaf (relabelTree swap (Frame.assemble U)).val r x}
      simpa [swap] using relabel_leaf_card swap (Frame.assemble U) p
    · letI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
      refine ⟨Equiv.refl _, ?_⟩
      intro T
      have hnAdj (x y : W) : ¬T.val.Adj x y := fun h ↦ h.ne (Subsingleton.elim _ _)
      apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
      intro x
      simp [Peak, RootedLeaf, hnAdj]

noncomputable def fixedRootEquiv [Finite V] [LinearOrder V] (r : V) : Tree V ≃ Tree V :=
  (fixedRootEquivSized (Nat.card V) V r rfl).val

theorem filterCard_eq_natCard [Fintype V] (P : V → Prop) :
    filterCard P = Nat.card {x // P x} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem fixedRootEquiv_filterCard [Fintype V] [LinearOrder V] (r : V) (T : Tree V) :
    filterCard (fun v ↦ ∀ w, T.val.Adj v w → w < v) =
      filterCard (fun v ↦ ¬ ∃ w, (fixedRootEquiv r T).val.Adj v w ∧
        (fixedRootEquiv r T).val.dist r v < (fixedRootEquiv r T).val.dist r w) := by
  rw [filterCard_eq_natCard, filterCard_eq_natCard]
  exact (fixedRootEquivSized (Nat.card V) V r rfl).prop T

end CayleyProbe
