/- GID: D5/S3/Combinatorics/SpectralGraph/MixedPowerExtrema
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/MixedPowerExtrema
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A path power minimizes the mixed largest eigenvalue and complete powers maximize it. -/

import D5.S3.Combinatorics.Graph.GraphDistance
import D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft
import D5.S3.Combinatorics.Graph.LinearForests.TreePathCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft
open Matrix Finset SimpleGraph
open D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation (graphPower)
open OmegaMath.RealRayleigh OmegaMath.MixedAdjacency OmegaMath.PairedEdgeEnergy OmegaMath.TreeGraft

noncomputable section

section PowerBand

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype V] [DecidableEq V] in
private theorem graphPower_mono {G H : SimpleGraph V} (hle : G ≤ H) (k : ℕ) :
    graphPower G k ≤ graphPower H k :=
  fun _ _ h => ⟨h.1, (SimpleGraph.edist_anti hle).trans h.2⟩

private def graphPowerIso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ) :
    graphPower G k ≃g graphPower H k where
  __ := e.toEquiv
  map_rel_iff' := by
    intro i j
    change (e i ≠ e j ∧ H.edist (e i) (e j) ≤ (k : ℕ∞)) ↔
      (i ≠ j ∧ G.edist i j ≤ (k : ℕ∞))
    rw [← edist_iso e]
    simp [e.injective.eq_iff]

omit [Fintype V] in
private theorem graphPower_complete_iff (G : SimpleGraph V) (hc : G.Connected) (k : ℕ) :
    graphPower G k = ⊤ ↔ ∀ i j, G.dist i j ≤ k := by
  constructor
  · intro he i j
    by_cases h : i = j
    · subst j
      simp
    · have hadj : (graphPower G k).Adj i j := by rw [he]; exact h
      exact (graphPower_adj_dist_iff G hc k i j).mp hadj |>.2
  · intro h
    ext i j
    rw [graphPower_adj_dist_iff G hc]
    exact ⟨fun h => h.1, fun h' => ⟨h', h i j⟩⟩

private theorem graphPower_complete_of_card (G : SimpleGraph V) (hc : G.Connected)
    {k : ℕ} (hk : Fintype.card V ≤ k + 1) :
    graphPower G k = ⊤ := by
  apply (graphPower_complete_iff G hc k).mpr
  intro i j
  have := dist_lt_card G hc i j
  omega

private theorem graphPower_upper (G : SimpleGraph V) (hc : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower G k) α ≤ (Fintype.card V : ℝ) - 1 ∧
      (mixedTop (graphPower G k) α = (Fintype.card V : ℝ) - 1 ↔
        ∀ i j, G.dist i j ≤ k) := by
  let := hc.nonempty
  exact ⟨mixedTop_le_complete _ hα hα', (mixedTop_eq_complete_iff _
    (graphPower_connected G hc hk) hα hα').trans (graphPower_complete_iff G hc k)⟩

private theorem path_iso_of_noncomplete_power (G : SimpleGraph V) (hc : G.Connected)
    {k : ℕ} (hk : Fintype.card V ≤ k + 2) (hn : graphPower G k ≠ ⊤) :
    Nonempty (pathGraph (Fintype.card V) ≃g G) := by
  have hnd : ¬ ∀ i j, G.dist i j ≤ k := fun h => hn ((graphPower_complete_iff G hc k).mpr h)
  push Not at hnd
  obtain ⟨i, j, hij⟩ := hnd
  have hlt := dist_lt_card G hc i j
  exact path_iso_of_dist_max G hc (by omega : G.dist i j + 1 = Fintype.card V)

private theorem pathGraph_power_noncomplete {n k : ℕ} (hk : k + 2 ≤ n) :
    graphPower (pathGraph n) k ≠ ⊤ := by
  have hn : n ≠ 0 := by omega
  have hc : (pathGraph n).Connected := SimpleGraph.connected_pathGraph.mpr hn
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨p, _, hp⟩ := hc.exists_path_of_dist i j
  have hb := (path_walk_length_bound p).1
  change n - 1 ≤ 0 + p.length at hb
  intro he
  have hle := (graphPower_complete_iff _ hc k).mp he i j
  omega

/-- The first nontrivial distance-power band, with both equality classes. -/
private theorem first_band (G : SimpleGraph V) (hc : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) (hband : Fintype.card V ≤ k + 2)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower (pathGraph (Fintype.card V)) k) α ≤ mixedTop (graphPower G k) α ∧
      mixedTop (graphPower G k) α ≤ (Fintype.card V : ℝ) - 1 ∧
      (mixedTop (graphPower G k) α =
        mixedTop (graphPower (pathGraph (Fintype.card V)) k) α ↔
        Fintype.card V ≤ k + 1 ∨ Nonempty (pathGraph (Fintype.card V) ≃g G)) ∧
      (mixedTop (graphPower G k) α = (Fintype.card V : ℝ) - 1 ↔
        ∀ i j, G.dist i j ≤ k) := by
  let := hc.nonempty
  let : Nonempty (Fin (Fintype.card V)) := ⟨⟨0, Fintype.card_pos⟩⟩
  let P := pathGraph (Fintype.card V)
  have hpconn : P.Connected := SimpleGraph.connected_pathGraph.mpr Fintype.card_pos.ne'
  have hupper := graphPower_upper G hc hk hα hα'
  have hpupper := graphPower_upper P hpconn hk hα hα'
  simp only [Fintype.card_fin] at hpupper
  have hmax_iff (J : SimpleGraph V) (hJ : J.Connected) :
      mixedTop (graphPower J k) α = (Fintype.card V : ℝ) - 1 ↔
        graphPower J k = ⊤ :=
    mixedTop_eq_complete_iff _ (graphPower_connected J hJ hk) hα hα'
  have hpmax_iff : mixedTop (graphPower P k) α = (Fintype.card V : ℝ) - 1 ↔
      graphPower P k = ⊤ := by
    simpa only [Fintype.card_fin] using
      mixedTop_eq_complete_iff (graphPower P k) (graphPower_connected P hpconn hk) hα hα'
  change mixedTop (graphPower P k) α ≤ mixedTop (graphPower G k) α ∧ _
  by_cases hwide : Fintype.card V ≤ k + 1
  · have hg := (hmax_iff G hc).mpr (graphPower_complete_of_card G hc hwide)
    have hp := hpmax_iff.mpr (graphPower_complete_of_card P hpconn (by simpa using hwide))
    refine ⟨?_, hupper.1, ?_, hupper.2⟩
    · rw [hg, hp]
    · rw [hg, hp]
      simp [hwide]
  · have hpne : graphPower P k ≠ ⊤ := pathGraph_power_noncomplete (by omega)
    have hplt : mixedTop (graphPower P k) α < (Fintype.card V : ℝ) - 1 :=
      lt_of_le_of_ne hpupper.1 (fun he => hpne (hpmax_iff.mp he))
    by_cases hg : graphPower G k = ⊤
    · have hgeq := (hmax_iff G hc).mpr hg
      have hl : mixedTop (graphPower P k) α < mixedTop (graphPower G k) α :=
        hgeq ▸ hplt
      refine ⟨hl.le, hupper.1, ?_, hupper.2⟩
      constructor
      · intro he
        exact (hl.ne he.symm).elim
      · rintro (h | he)
        · exact (hwide h).elim
        · obtain ⟨e⟩ := he
          exact (mixedTop_iso (graphPowerIso e k) α).symm
    · obtain ⟨e⟩ := path_iso_of_noncomplete_power G hc hband hg
      have he := mixedTop_iso (graphPowerIso e k) α
      refine ⟨he.le, hupper.1, ?_, hupper.2⟩
      exact ⟨fun _ => Or.inr ⟨e⟩, fun _ => he.symm⟩

end D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

end PowerBand

section TreeDescent

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.LeafTransfer

variable {V : Type*} {T : SimpleGraph V}

private theorem parent_unique (hT : T.IsTree) (r : V) {v x y : V}
    (hx : T.Adj v x) (hy : T.Adj v y)
    (hdx : T.dist r v = T.dist r x + 1) (hdy : T.dist r v = T.dist r y + 1) :
    x = y := by
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist r x
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist r y
  have hpx : (p.concat hx.symm).length = T.dist r v := by rw [Walk.length_concat, hp, hdx]
  have hqy : (q.concat hy.symm).length = T.dist r v := by rw [Walk.length_concat, hq, hdy]
  obtain ⟨_, _, hu⟩ := hT.existsUnique_path r v
  have he := (hu _ ((p.concat hx.symm).isPath_of_length_eq_dist hpx)).trans
    (hu _ ((q.concat hy.symm).isPath_of_length_eq_dist hqy)).symm
  have h := congrArg (fun w : T.Walk r v => w.penultimate) he
  simpa using h

section Arms

variable [Fintype V] [DecidableRel T.Adj]

private theorem two_children (hT : T.IsTree) (r v : V) (hv : 3 ≤ T.degree v) :
    ∃ x y, x ≠ y ∧ T.Adj v x ∧ T.Adj v y ∧
      T.dist r x = T.dist r v + 1 ∧ T.dist r y = T.dist r v + 1 := by
  classical
  let parent := (T.neighborFinset v).filter (fun x => T.dist r v = T.dist r x + 1)
  let child := (T.neighborFinset v).filter (fun x => T.dist r x = T.dist r v + 1)
  have hp : parent.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    simp only [parent, Finset.mem_filter, mem_neighborFinset]
    intro x hx y hy
    exact parent_unique hT r hx.1 hy.1 hx.2 hy.2
  have hcover : T.neighborFinset v ⊆ parent ∪ child := by
    intro x hx
    have hx' := (mem_neighborFinset T v x).mp hx
    rcases hT.dist_eq_dist_add_one_of_adj r hx' with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hc : 1 < child.card := by
    have h := (Finset.card_le_card hcover).trans (Finset.card_union_le parent child)
    rw [card_neighborFinset_eq_degree] at h
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  simp only [child, Finset.mem_filter, mem_neighborFinset] at hx hy
  exact ⟨x, y, hxy, hx.1, hy.1, hx.2, hy.2⟩

/-- Extend the specified outward edge to a terminal arm when deeper vertices do
not branch. Distances from the fixed root increase along the whole arm. -/
private theorem exists_outward_arm (hT : T.IsTree) (r : V) {v y : V}
    (hy : T.Adj v y) (hdy : T.dist r y = T.dist r v + 1)
    (hfar : ∀ w, T.dist r v < T.dist r w → T.degree w ≤ 2) :
    ∃ (a : ℕ) (X : PendantArm T v a) (ha : 1 ≤ a), X.first ha = y ∧
      ∀ i : Fin (a + 1), T.dist r (X.path i) = T.dist r v + i.val := by
  classical
  let descendants := Finset.univ.filter (fun w => T.dist r w = T.dist r y + T.dist y w)
  have hmem : y ∈ descendants := by simp [descendants]
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image descendants (T.dist r) ⟨y, hmem⟩
  have hdu : T.dist r u = T.dist r y + T.dist y u := (Finset.mem_filter.mp hu).2
  have hno (w : V) (hw : T.Adj u w) : T.dist r w ≠ T.dist r u + 1 := by
    intro hd
    have hlo := hT.connected.dist_triangle (u := r) (v := y) (w := w)
    have hhi := hT.connected.dist_triangle (u := y) (v := u) (w := w)
    rw [dist_eq_one_iff_adj.mpr hw] at hhi
    have hw' : w ∈ descendants := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have := hmax w hw'
    omega
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist r v
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist y u
  let s := q.cons hy
  have hlen : s.length = T.dist y u + 1 := by simp [s, hq]
  have hs : (p.append s).length = T.dist r u := by
    rw [Walk.length_append, hp, hlen]
    omega
  have hdepth (i : ℕ) (hi : i ≤ s.length) :
      T.dist r (s.getVert i) = T.dist r v + i := by
    have h := dist_eq_index_of_shortest hT.connected (p.append s) hs (p.length + i)
      (by rw [Walk.length_append]; omega)
    rw [Walk.getVert_append, ite_eq_right (by omega : ¬ p.length + i < p.length),
      Nat.add_sub_cancel_left, hp] at h
    exact h
  have ha : 1 ≤ s.length := by omega
  let f : pathGraph (s.length + 1) →g T := {
    toFun i := s.getVert i.val
    map_rel' := by
      intro i j hij
      rcases pathGraph_adj.mp hij with h | h
      · rw [← h]
        exact s.adj_getVert_succ (by have := j.isLt; omega)
      · rw [← h]
        exact (s.adj_getVert_succ (by have := i.isLt; omega)).symm }
  have htip : T.degree u = 1 := by
    let t := s.length - 1
    have ht : t < s.length := by dsimp [t]; omega
    have htu : t + 1 = s.length := by dsimp [t]; omega
    have hadj := (s.adj_getVert_succ ht).symm
    rw [htu, Walk.getVert_length] at hadj
    refine degree_eq_one_iff_existsUnique_adj.mpr ⟨s.getVert t, hadj, ?_⟩
    intro w hw
    rcases hT.dist_eq_dist_add_one_of_adj r hw with hd | hd
    · apply parent_unique hT r hw hadj hd
      have h := hdepth t ht.le
      rw [h, hdu, hdy]
      omega
    · exact (hno w hw hd).elim
  let X : PendantArm T v s.length := {
    path := f
    injective := by
      intro i j he
      apply Fin.ext
      change s.getVert i.val = s.getVert j.val at he
      have hi := hdepth i.val (by have := i.isLt; omega)
      have hj := hdepth j.val (by have := j.isLt; omega)
      rw [he, hj] at hi
      omega
    root := s.getVert_zero
    tip_degree := by
      change T.degree (s.getVert s.length) = 1
      rw [Walk.getVert_length]
      exact htip
    internal_degree := by
      intro i hi hj
      change T.degree (s.getVert i.val) = 2
      have h := hdepth i.val hj.le
      have hlo := hfar (s.getVert i.val) (by omega)
      have hp := s.adj_getVert_succ (i := i.val - 1) (by omega)
      have he : i.val - 1 + 1 = i.val := by omega
      rw [he] at hp
      have hn := s.adj_getVert_succ hj
      have hpdepth := hdepth (i.val - 1) (by omega)
      have hndepth := hdepth (i.val + 1) (by omega)
      have hne : s.getVert (i.val - 1) ≠ s.getVert (i.val + 1) := by
        intro he
        rw [he, hndepth] at hpdepth
        omega
      have hsub : ({s.getVert (i.val - 1), s.getVert (i.val + 1)} : Finset V) ⊆
          T.neighborFinset (s.getVert i.val) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (mem_neighborFinset _ _ _).mpr hp.symm
        · obtain rfl := Finset.mem_singleton.mp hw
          exact (mem_neighborFinset _ _ _).mpr hn
      have hhi := Finset.card_le_card hsub
      simp only [Finset.card_pair hne, card_neighborFinset_eq_degree] at hhi
      omega }
  exact ⟨s.length, X, ha, by change s.getVert 1 = y; simp [s],
    fun i => hdepth i.val (by have := i.isLt; omega)⟩

/-- A farthest branching vertex has two terminal arms directed away from the
fixed vertex. The arms are ordered so that the shorter arm can donate its tip. -/
private theorem exists_outward_terminal_arms (hT : T.IsTree) (r : V)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V))) :
    ∃ (v : V) (a b : ℕ) (X : PendantArm T v a) (Y : PendantArm T v b)
      (hb : 1 ≤ b) (hab : b ≤ a),
      3 ≤ T.degree v ∧
      (∀ w, 3 ≤ T.degree w → T.dist r w ≤ T.dist r v) ∧
      X.first (hb.trans hab) ≠ Y.first hb ∧
      (∀ i : Fin (a + 1), T.dist r (X.path i) = T.dist r v + i.val) ∧
      (∀ j : Fin (b + 1), T.dist r (Y.path j) = T.dist r v + j.val) := by
  classical
  let branches := Finset.univ.filter (fun w => 3 ≤ T.degree w)
  have hne : branches.Nonempty := by
    by_contra hn
    apply hNonpath
    obtain ⟨n, ⟨e⟩⟩ := OneJoinedPathTrees.path_of_degree_le_two hT (fun w => by
      rw [OneJoinedPathTrees.degree, T.ncard_neighborSet]
      by_contra hd
      exact hn ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    have hncard : n + 1 = Fintype.card V := by
      simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
    exact ⟨hncard ▸ e.symm⟩
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image branches (T.dist r) hne
  have hvdeg : 3 ≤ T.degree v := (Finset.mem_filter.mp hv).2
  have hmax' (w : V) (hw : 3 ≤ T.degree w) : T.dist r w ≤ T.dist r v :=
    hmax w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
  have hfar (w : V) (hw : T.dist r v < T.dist r w) : T.degree w ≤ 2 := by
    by_contra hd
    have := hmax' w (by omega)
    omega
  obtain ⟨x, y, hxy, hx, hy, hdx, hdy⟩ := two_children hT r v hvdeg
  obtain ⟨a, X, ha, hX, hXd⟩ := exists_outward_arm hT r hx hdx hfar
  obtain ⟨b, Y, hb, hY, hYd⟩ := exists_outward_arm hT r hy hdy hfar
  rcases le_total b a with hab | hba
  · exact ⟨v, a, b, X, Y, hb, hab, hvdeg, hmax', by simpa only [hX, hY], hXd, hYd⟩
  · exact ⟨v, b, a, Y, X, ha, hba, hvdeg, hmax', by simpa only [hX, hY] using hxy.symm,
      hYd, hXd⟩

end Arms
/-- The sum of the deficits of the distances from a fixed vertex. -/
private noncomputable def depthDeficit [Fintype V] (r : V) (T : SimpleGraph V) : ℕ :=
  ∑ w : V, (Fintype.card V - T.dist r w)

namespace PendantArm

variable [Fintype V] [DecidableRel T.Adj] {v : V} {a b : ℕ}
variable (X : PendantArm T v a) (Y : PendantArm T v b)
private theorem move_isTree (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) : (X.move Y hb).IsTree := by
  have h := (X.terminalArms Y hT hb hab hfirst).graft_tree hT
  rw [X.terminalArms_right Y hT hb hab hfirst, ← X.move_eq_graft Y hT hb hab hfirst] at h
  exact h

/-- An outward M1 increases the moved tip's depth by `a - b + 1` and
preserves the depths of all other vertices. -/
private theorem move_dist_from_root (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) (r : V)
    (hX : ∀ i : Fin (a + 1), T.dist r (X.path i) = T.dist r v + i.val)
    (hY : ∀ j : Fin (b + 1), T.dist r (Y.path j) = T.dist r v + j.val) :
    let z := Y.path (Fin.last b)
    (X.move Y hb).dist r z = T.dist r z + (a - b + 1) ∧
      ∀ w, w ≠ z → (X.move Y hb).dist r w = T.dist r w := by
  dsimp only
  let z := Y.path (Fin.last b)
  let A := X.terminalArms Y hT hb hab hfirst
  let t := A.q (Fin.last (a + b - 1))
  have hright : t.val = X.path (Fin.last a) := X.terminalArms_right Y hT hb hab hfirst
  have hdz : T.dist r z = T.dist r v + b := hY (Fin.last b)
  have hrz : r ≠ z := by
    intro he
    rw [← he, SimpleGraph.dist_self] at hdz
    omega
  let r' : Surviving z := ⟨r, hrz⟩
  have hg : X.move Y hb = graft T z t.val :=
    (X.move_eq_graft Y hT hb hab hfirst).trans (congrArg (graft T z) hright.symm)
  have ht := graft_dist_surviving hT A.leaf t t r'
  have hnew := leaf_dist (A.graft_tree hT).connected (graft_adj_leaf t.property) t rfl r'
  have hnew' : (X.move Y hb).dist r z = 1 + T.dist r t.val := by
    rw [hg, SimpleGraph.dist_comm (u := r), hnew, surviving_graft, ← ht.2, SimpleGraph.dist_comm (v := r)]
  refine ⟨?_, ?_⟩
  · change (X.move Y hb).dist r z = T.dist r z + (a - b + 1)
    rw [hnew', hright, hX (Fin.last a), hdz, Fin.val_last]
    omega
  · intro w hw
    have h := graft_dist_surviving hT A.leaf t r' ⟨w, hw⟩
    rw [hg]
    exact h.1.trans h.2.symm

private theorem depthDeficit_move_lt (hT : T.IsTree) (hb : 1 ≤ b) (hab : b ≤ a)
    (hfirst : X.first (hb.trans hab) ≠ Y.first hb) (r : V)
    (hX : ∀ i : Fin (a + 1), T.dist r (X.path i) = T.dist r v + i.val)
    (hY : ∀ j : Fin (b + 1), T.dist r (Y.path j) = T.dist r v + j.val) :
    depthDeficit r (X.move Y hb) < depthDeficit r T := by
  classical
  obtain ⟨htip, hother⟩ := PendantArm.move_dist_from_root X Y hT hb hab hfirst r hX hY
  have hlt : T.dist r (Y.path (Fin.last b)) < (X.move Y hb).dist r (Y.path (Fin.last b)) := by
    rw [htip]
    omega
  have hstrict : Fintype.card V - (X.move Y hb).dist r (Y.path (Fin.last b)) <
      Fintype.card V - T.dist r (Y.path (Fin.last b)) :=
    Nat.sub_lt_sub_left (dist_lt_card T hT.connected r _) hlt
  unfold depthDeficit
  apply Finset.sum_lt_sum
  · intro w _
    by_cases hw : w = Y.path (Fin.last b)
    · exact hw ▸ hstrict.le
    · rw [hother w hw]
  · exact ⟨Y.path (Fin.last b), Finset.mem_univ _, hstrict⟩

end PendantArm

open scoped Classical in
/-- One source M1 on a nonpath tree, using arms directed away from the fixed
vertex `r`. Both the source and target graphs have the original carrier. -/
private noncomputable def RootedM1 [Fintype V] (r : V) (T U : SimpleGraph V) : Prop :=
  T.IsTree ∧ ¬ Nonempty (T ≃g pathGraph (Fintype.card V)) ∧
  ∃ (v : V) (a b : ℕ) (X : PendantArm T v a) (Y : PendantArm T v b)
    (hb : 1 ≤ b) (hab : b ≤ a),
    3 ≤ T.degree v ∧ X.first (hb.trans hab) ≠ Y.first hb ∧
    (∀ i : Fin (a + 1), T.dist r (X.path i) = T.dist r v + i.val) ∧
    (∀ j : Fin (b + 1), T.dist r (Y.path j) = T.dist r v + j.val) ∧
    U = X.move Y hb

namespace RootedM1

variable [Fintype V] {r : V} {U : SimpleGraph V}

private theorem exists_step (hT : T.IsTree) (hn : ¬ Nonempty (T ≃g pathGraph (Fintype.card V))) :
    ∃ U, RootedM1 r T U := by
  classical
  obtain ⟨v, a, b, X, Y, hb, hab, hv, _, hfirst, hX, hY⟩ :=
    exists_outward_terminal_arms hT r hn
  exact ⟨_, hT, hn, v, a, b, X, Y, hb, hab, hv, hfirst, hX, hY, rfl⟩

private theorem target_tree (h : RootedM1 r T U) : U.IsTree := by
  classical
  obtain ⟨hT, _, _, _, _, X, Y, hb, hab, _, hfirst, _, _, rfl⟩ := h
  exact PendantArm.move_isTree X Y hT hb hab hfirst

private theorem decreases (h : RootedM1 r T U) : depthDeficit r U < depthDeficit r T := by
  classical
  obtain ⟨hT, _, _, _, _, X, Y, hb, hab, _, hfirst, hX, hY, rfl⟩ := h
  exact PendantArm.depthDeficit_move_lt X Y hT hb hab hfirst r hX hY

/-- Every finite tree reaches a path by a finite sequence of rooted M1 moves. -/
private theorem reaches_path (r : V) (hT : T.IsTree) :
    ∃ P, Relation.ReflTransGen (RootedM1 r) T P ∧ P.IsTree ∧
      Nonempty (P ≃g pathGraph (Fintype.card V)) := by
  induction T using (measure (depthDeficit r)).wf.induction with
  | h T ih =>
    classical
    by_cases hp : Nonempty (T ≃g pathGraph (Fintype.card V))
    · exact ⟨T, .refl, hT, hp⟩
    · obtain ⟨U, hu⟩ := exists_step (r := r) hT hp
      obtain ⟨P, hUP, hP, hiso⟩ := ih U hu.decreases hu.target_tree
      exact ⟨P, hUP.head hu, hP, hiso⟩

/-- A nonpath tree reaches a path by a nonempty sequence. The displayed last
move starts at a nonpath tree, as required for the strict comparison. -/
private theorem reaches_path_with_last (r : V) (hT : T.IsTree)
    (hn : ¬ Nonempty (T ≃g pathGraph (Fintype.card V))) :
    ∃ U P, Relation.ReflTransGen (RootedM1 r) T U ∧
      RootedM1 r U P ∧ Nonempty (P ≃g pathGraph (Fintype.card V)) := by
  obtain ⟨P, hTP, _, hiso⟩ := reaches_path r hT
  rcases hTP.cases_tail with he | ⟨U, hTU, hUP⟩
  · exact (hn (he ▸ hiso)).elim
  · exact ⟨U, P, hTU, hUP, hiso⟩

end RootedM1

end D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.LeafTransfer

end TreeDescent

section TreeExtremum

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.LeafTransfer

variable {V : Type*} [Fintype V] [DecidableEq V] {T U : SimpleGraph V}

namespace RootedM1

variable {r : V}

private theorem mixedTop_step_le (h : RootedM1 r T U) {k : ℕ} (hk : 1 ≤ k)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) :
    mixedTop (graphPower U k) α ≤ mixedTop (graphPower T k) α := by
  classical
  obtain ⟨hT, _, _, _, _, X, Y, hb, hab, _, hfirst, _, _, rfl⟩ := h
  exact X.mixedTop_move_le Y hT hb hab hfirst hk hα hα'

private theorem mixedTop_chain_le (h : Relation.ReflTransGen (RootedM1 r) T U) {k : ℕ} (hk : 1 ≤ k)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) :
    mixedTop (graphPower U k) α ≤ mixedTop (graphPower T k) α := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (hstep.mixedTop_step_le hk hα hα').trans ih

private theorem mixedTop_last_step_lt (h : RootedM1 r T U)
    (hPath : Nonempty (U ≃g pathGraph (Fintype.card V)))
    {k : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ Fintype.card V)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower U k) α < mixedTop (graphPower T k) α := by
  classical
  obtain ⟨hT, hNonpath, _, _, _, X, Y, hb, hab, _, hfirst, _, _, rfl⟩ := h
  exact X.mixedTop_last_move_lt Y hT hb hab hfirst hNonpath hPath hk hn hα hα'

end RootedM1

omit [DecidableEq V] in
private theorem nonempty_path_carrier (hT : T.IsTree) : Nonempty (Fin (Fintype.card V)) := by
  let := hT.connected.nonempty
  exact ⟨⟨0, Fintype.card_pos⟩⟩

/-- The path minimizes the mixed top eigenvalue of the kth power over trees. -/
private theorem mixedTop_tree_ge_path (hT : T.IsTree) {k : ℕ} (hk : 1 ≤ k)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) :
    mixedTop (graphPower (pathGraph (Fintype.card V)) k) α ≤ mixedTop (graphPower T k) α := by
  let := hT.connected.nonempty
  let := nonempty_path_carrier hT
  obtain ⟨r⟩ := hT.connected.nonempty
  obtain ⟨P, hTP, _, ⟨e⟩⟩ := RootedM1.reaches_path r hT
  rw [← mixedTop_iso (graphPowerIso e k) α]
  exact RootedM1.mixedTop_chain_le hTP hk hα hα'

/-- At and above order `k + 2`, for `k ≥ 2`, the path has strictly smaller
mixed top eigenvalue than every nonpath tree of the same order. -/
private theorem mixedTop_tree_gt_path_of_nonpath (hT : T.IsTree)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V)))
    {k : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ Fintype.card V)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower (pathGraph (Fintype.card V)) k) α < mixedTop (graphPower T k) α := by
  let := hT.connected.nonempty
  let := nonempty_path_carrier hT
  obtain ⟨r⟩ := hT.connected.nonempty
  obtain ⟨U, P, hTU, hUP, hPath⟩ := RootedM1.reaches_path_with_last r hT hNonpath
  rw [← mixedTop_iso (graphPowerIso hPath.some k) α]
  exact (hUP.mixedTop_last_step_lt hPath hk hn hα hα').trans_le
    (RootedM1.mixedTop_chain_le hTU (by omega) hα hα'.le)

end D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.LeafTransfer

end TreeExtremum

section FirstPowerTree

open scoped Classical

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.LeafTransfer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every nonpath tree has larger first-power value than the path at the same order. -/
private theorem mixedTop_tree_one_gt_path_of_nonpath {T : SimpleGraph V} (hT : T.IsTree)
    (hNonpath : ¬ Nonempty (T ≃g pathGraph (Fintype.card V)))
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower (pathGraph (Fintype.card V)) 1) α < mixedTop (graphPower T 1) α := by
  let := hT.connected.nonempty
  let : Nonempty (Fin (Fintype.card V)) := ⟨⟨0, Fintype.card_pos⟩⟩
  obtain ⟨r⟩ := hT.connected.nonempty
  obtain ⟨U, P, hTU, hUP, ⟨e⟩⟩ := RootedM1.reaches_path_with_last r hT hNonpath
  rw [← mixedTop_iso (graphPowerIso e 1) α]
  apply lt_of_lt_of_le _ (RootedM1.mixedTop_chain_le hTU (by decide) hα hα'.le)
  obtain ⟨hU, hNonpathU, _, _, _, X, Y, hb, hab, _, hfirst, _, _, rfl⟩ := hUP
  rw [X.move_eq_graft Y hU hb hab hfirst, ← X.terminalArms_right Y hU hb hab hfirst] at e ⊢
  exact (X.terminalArms Y hU hb hab hfirst).mixedTop_last_graft_one_lt hU hNonpathU ⟨e⟩ hα hα'

end D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.LeafTransfer

end FirstPowerTree

section SpanningPathPower

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

variable {V : Type*} [Fintype V] [DecidableEq V] {G T : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
/-- Above the complete-power range, an extra edge across a spanning path gives
an edge of the larger power absent from the path power. -/
private theorem graphPower_lt_of_spanning_path {n k : ℕ}
    (e : pathGraph n ≃g T) (hTG : T < G) (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    graphPower T k < graphPower G k := by
  have hP : (pathGraph n).Connected := connected_pathGraph.mpr (by omega)
  have hT : T.Connected := hP.map e.toHom e.surjective
  have hG : G.Connected := hT.mono hTG.le
  let f : pathGraph n →g G := (Hom.ofLE hTG.le).comp e.toHom
  have pathDist (i j : Fin n) (hij : i.val ≤ j.val) :
      T.dist (e i) (e j) = j.val - i.val := by
    have h := congrArg ENat.toNat (edist_iso e i j)
    change (pathGraph n).dist i j = T.dist (e i) (e j) at h
    rw [← h, OmegaMath.Combinatorics.Graph.GraphDistance.pathGraph_dist, Nat.dist_eq_sub_of_le hij]
  have edge (i j : Fin n) (hij : i.val < j.val)
      (h : G.Adj (e i) (e j)) (hchord : ¬ T.Adj (e i) (e j)) :
      ∃ u v, (graphPower G k).Adj (e u) (e v) ∧
        ¬ (graphPower T k).Adj (e u) (e v) := by
    have hgap : i.val + 2 ≤ j.val := by
      by_contra! hsmall
      exact hchord (e.toHom.map_rel (pathGraph_adj.mpr (Or.inl (by omega))))
    by_cases hfar : k < j.val - i.val
    · have hadj : (graphPower G k).Adj (e i) (e j) :=
        (graphPower_adj_dist_iff G hG k _ _).mpr ⟨h.ne, (dist_eq_one_iff_adj.mpr h).le.trans hk⟩
      refine ⟨i, j, hadj, ?_⟩
      rw [graphPower_adj_dist_iff T hT, pathDist i j hij.le]
      omega
    let t := min i.val (k + 1 - (j.val - i.val))
    let u : Fin n := ⟨i.val - t, Nat.lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩
    let v : Fin n := ⟨u.val + k + 1, by
      have := j.isLt
      dsimp [u, t]
      rw [min_def]
      split <;> omega⟩
    have hui : u.val ≤ i.val := Nat.sub_le ..
    have hjv : j.val ≤ v.val := by
      dsimp [v, u, t]
      rw [min_def]
      split <;> omega
    have huv : u.val < v.val := by dsimp [v]; omega
    obtain ⟨p, hp⟩ := hP.exists_walk_length_eq_dist u i
    obtain ⟨q, hq⟩ := hP.exists_walk_length_eq_dist j v
    have hp' : p.length = i.val - u.val := by
      rw [hp, OmegaMath.Combinatorics.Graph.GraphDistance.pathGraph_dist, Nat.dist_eq_sub_of_le hui]
    have hq' : q.length = v.val - j.val := by
      rw [hq, OmegaMath.Combinatorics.Graph.GraphDistance.pathGraph_dist, Nat.dist_eq_sub_of_le hjv]
    have hEdge : G.Adj (f i) (f j) := h
    let w := (p.map f).append ((q.map f).cons hEdge)
    have hw : w.length ≤ k := by
      dsimp only [w]
      rw [Walk.length_append, Walk.length_cons, Walk.length_map, Walk.length_map, hp', hq']
      have hv : v.val = u.val + k + 1 := rfl
      omega
    refine ⟨u, v, ?_, ?_⟩
    · exact (graphPower_adj_dist_iff G hG k _ _).mpr
        ⟨e.injective.ne (Fin.ne_of_lt huv), (dist_le w).trans hw⟩
    · rw [graphPower_adj_dist_iff T hT, pathDist u v huv.le]
      have hv : v.val = u.val + k + 1 := rfl
      omega
  refine lt_of_le_of_ne (graphPower_mono hTG.le k) fun hp => hTG.not_ge ?_
  intro a b hab
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  by_contra hchord
  have hij : i.val ≠ j.val := fun he => hab.ne (congrArg e (Fin.ext he))
  obtain ⟨u, v, huv, hnot⟩ := (lt_or_gt_of_ne hij).elim
    (fun h => edge i j h hab hchord)
    (fun h => edge j i h hab.symm (fun ha => hchord ha.symm))
  exact hnot (hp ▸ huv)

end D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

end SpanningPathPower

section Extrema

namespace D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Das–Ashni–Sangeetha, Question 5.1. The path minimizes the real largest
eigenvalue of the mixed matrix of the distance power. The upper value is
attained exactly by graphs in which all vertex distances are at most k. -/
theorem result (G : SimpleGraph V) (hc : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    mixedTop (graphPower (pathGraph (Fintype.card V)) k) α ≤ mixedTop (graphPower G k) α ∧
      mixedTop (graphPower G k) α ≤ (Fintype.card V : ℝ) - 1 ∧
      (mixedTop (graphPower G k) α =
        mixedTop (graphPower (pathGraph (Fintype.card V)) k) α ↔
        Fintype.card V ≤ k + 1 ∨ Nonempty (pathGraph (Fintype.card V) ≃g G)) ∧
      (mixedTop (graphPower G k) α = (Fintype.card V : ℝ) - 1 ↔
        ∀ i j, G.dist i j ≤ k) := by
  by_cases hband : Fintype.card V ≤ k + 2
  · exact first_band G hc hk hband hα hα'
  let := hc.nonempty
  let : Nonempty (Fin (Fintype.card V)) := ⟨⟨0, Fintype.card_pos⟩⟩
  obtain ⟨T, hTG, hT⟩ := hc.exists_isTree_le
  have hpower := graphPower_mono hTG k
  have hmono := mixedTop_mono hpower hα hα'.le
  have hmin := LeafTransfer.mixedTop_tree_ge_path hT hk hα hα'.le
  have hupper := graphPower_upper G hc hk hα hα'
  refine ⟨hmin.trans hmono, hupper.1, ?_, hupper.2⟩
  constructor
  · intro he
    have heT := le_antisymm (hmono.trans_eq he) hmin
    have hPath : Nonempty (T ≃g pathGraph (Fintype.card V)) := by
      by_contra hn
      have hstrict : mixedTop (graphPower (pathGraph (Fintype.card V)) k) α <
          mixedTop (graphPower T k) α := by
        by_cases h1 : k = 1
        · subst k
          exact LeafTransfer.mixedTop_tree_one_gt_path_of_nonpath hT hn hα hα'
        · exact LeafTransfer.mixedTop_tree_gt_path_of_nonpath hT hn (by omega)
            (by omega) hα hα'
      exact hstrict.ne heT.symm
    obtain ⟨e⟩ := hPath
    have hEq : T = G := by
      by_contra hne
      have hp := graphPower_lt_of_spanning_path e.symm (lt_of_le_of_ne hTG hne) hk (by omega)
      have hstrict := mixedTop_strict hp (graphPower_connected T hT.connected hk) hα hα'
      exact (hmin.trans_lt hstrict).ne he.symm
    exact Or.inr ⟨hEq ▸ e.symm⟩
  · intro he
    rcases he with hsmall | hPath
    · exact (hband (by omega)).elim
    · obtain ⟨e⟩ := hPath
      exact (mixedTop_iso (graphPowerIso e k) α).symm

end D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

end Extrema
