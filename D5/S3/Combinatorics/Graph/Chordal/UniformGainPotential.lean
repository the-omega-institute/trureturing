/- GID: D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/UniformGainPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle defects bound chordal gain errors independently of graph size. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.Topology.MetricSpace.IsometricSMul

/-! # Uniform approximation of group gains on chordal graphs

The shadow of a component above a distance layer is a clique. Its predecessors in the
parent shadow are nested, so the component has an anchor adjacent to its entire shadow.
The resulting potential uses at most four triangle comparisons across an edge.
-/

universe u v

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

private theorem geodesic_edge {x y : V} (p : G.Walk x y) (hp : p.length = G.dist x y)
    {a b : V} (ha : a ∈ p.support) (hb : b ∈ p.support) (hab : G.Adj a b) :
    s(a, b) ∈ p.edges := by
  classical
  obtain ⟨r, t, rfl⟩ : ∃ (r : G.Walk x a) (t : G.Walk a y), p = r.append t :=
    ⟨p.takeUntil a ha, p.dropUntil a ha, (p.take_spec ha).symm⟩
  rcases (Walk.mem_support_append_iff r t).mp hb with hb | hb
  · obtain ⟨r', m, rfl⟩ : ∃ (r' : G.Walk x b) (m : G.Walk b a), r = r'.append m :=
      ⟨r.takeUntil b hb, r.dropUntil b hb, (r.take_spec hb).symm⟩
    have hm := length_eq_dist_of_subwalk hp (show m.IsSubwalk ((r'.append m).append t) from
      ⟨r', t, rfl⟩)
    have hme : m = hab.symm.toWalk :=
      Walk.eq_of_length_le_one (by simpa [dist_eq_one_iff_adj.mpr hab.symm] using hm.le)
        (by simp)
    simp [Walk.edges_append, hme, Sym2.eq_swap]
  · obtain ⟨m, t', rfl⟩ : ∃ (m : G.Walk a b) (t' : G.Walk b y), t = m.append t' :=
      ⟨t.takeUntil b hb, t.dropUntil b hb, (t.take_spec hb).symm⟩
    have hm := length_eq_dist_of_subwalk hp (show m.IsSubwalk (r.append (m.append t')) from
      ⟨r, t', Walk.append_assoc r m t'⟩)
    have hme : m = hab.toWalk :=
      Walk.eq_of_length_le_one (by simpa [dist_eq_one_iff_adj.mpr hab] using hm.le) (by simp)
    simp [Walk.edges_append, hme]

private theorem induced_path {S : Set V} {x y : V} {hx : x ∈ S} {hy : y ∈ S}
    (h : (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ p : G.Walk x y, p.IsPath ∧ (∀ w ∈ p.support, w ∈ S) ∧
      (∀ a ∈ p.support, ∀ b ∈ p.support, G.Adj a b → s(a, b) ∈ p.edges) := by
  obtain ⟨p, hp, hd⟩ := h.exists_path_of_dist
  let f : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  refine ⟨p.map f, hp.map Subtype.val_injective, ?_, ?_⟩
  · intro w hw
    replace hw : w ∈ List.map (⇑f) p.support := (Walk.support_map f p) ▸ hw
    obtain ⟨w', _, rfl⟩ := List.mem_map.mp hw
    exact w'.property
  · intro a ha b hb hab
    replace ha : a ∈ List.map (⇑f) p.support := (Walk.support_map f p) ▸ ha
    replace hb : b ∈ List.map (⇑f) p.support := (Walk.support_map f p) ▸ hb
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    apply (Walk.edges_map f p).symm ▸ (?_ : _ ∈ List.map (Sym2.map ⇑f) p.edges)
    exact List.mem_map.mpr ⟨s(a', b'), geodesic_edge p hd ha' hb' hab, rfl⟩

private theorem separated_paths (hG : G.IsChordal) {x y : V} (hxy : x ≠ y)
    (hn : ¬ G.Adj x y) {S T : Set V} {hxS : x ∈ S} {hyS : y ∈ S}
    {hxT : x ∈ T} {hyT : y ∈ T}
    (hs : (G.induce S).Reachable ⟨x, hxS⟩ ⟨y, hyS⟩)
    (ht : (G.induce T).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩)
    (hsep : ∀ a ∈ S, ∀ b ∈ T, a ≠ x → a ≠ y → b ≠ x → b ≠ y →
      a ≠ b ∧ ¬ G.Adj a b) : False := by
  obtain ⟨p, hp, hps, hpe⟩ := induced_path hs
  obtain ⟨q, hq, hqt, hqe⟩ := induced_path ht
  have length_ge_two (w : G.Walk x y) : 2 ≤ w.length := by
    cases w with
    | nil => exact (hxy rfl).elim
    | cons h w =>
      cases w with
      | nil => exact (hn h).elim
      | cons _ _ => simp [Walk.length_cons]
  have hp2 := length_ge_two p
  have hq2 := length_ge_two q
  have start_not_mem_tail {a b : V} {w : G.Walk a b} (hw : w.IsPath) :
      a ∉ w.support.tail := by
    have hd := hw.support_nodup
    rw [← Walk.cons_tail_support] at hd
    exact (List.nodup_cons.mp hd).1
  have disjoint : p.support.tail.Disjoint q.reverse.support.tail := by
    intro w hwp hwq
    have hwq' : w ∈ q.support := by
      simpa using List.mem_of_mem_tail hwq
    have hwx : w ≠ x := fun e => start_not_mem_tail hp (e ▸ hwp)
    have hwy : w ≠ y := fun e => start_not_mem_tail hq.reverse (e ▸ hwq)
    exact (hsep w (hps w (List.mem_of_mem_tail hwp)) w (hqt w hwq') hwx hwy hwx hwy).1 rfl
  have hc := hp.isCycle_append hq.reverse disjoint (Or.inl (by omega))
  have hl : 4 ≤ (p.append q.reverse).length := by
    rw [Walk.length_append, Walk.length_reverse]
    omega
  obtain ⟨a, b, ha, hb, hab, he⟩ := hG (p.append q.reverse) hc hl
  apply he
  rw [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse]
  have cross {a b : V} (ha : a ∈ p.support) (hb : b ∈ q.support) (hab : G.Adj a b) :
      s(a, b) ∈ p.edges ∨ s(a, b) ∈ q.edges := by
    by_cases hax : a = x
    · exact Or.inr (hqe _ (hax ▸ q.start_mem_support) _ hb hab)
    by_cases hay : a = y
    · exact Or.inr (hqe _ (hay ▸ q.end_mem_support) _ hb hab)
    by_cases hbx : b = x
    · exact Or.inl (hpe _ ha _ (hbx ▸ p.start_mem_support) hab)
    by_cases hby : b = y
    · exact Or.inl (hpe _ ha _ (hby ▸ p.end_mem_support) hab)
    exact ((hsep _ (hps _ ha) _ (hqt _ hb) hax hay hbx hby).2 hab).elim
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inl (hpe _ ha _ hb hab)
  · exact cross ha hb hab
  · rw [Sym2.eq_swap]
    exact cross hb ha hab.symm
  · exact Or.inr (hqe _ ha _ hb hab)

private theorem four_cycle_diagonal (hG : G.IsChordal) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : G.Adj a c ∨ G.Adj b d := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd hda.toWalk))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [p, Walk.isPath_def, hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
  obtain ⟨x, y, hx, hy, hxy, hchord⟩ := hG p hp (by simp [p])
  simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx hy
  simp only [p, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hchord
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    first | exact (hxy.ne rfl).elim | exact Or.inl hxy | exact Or.inl hxy.symm |
      exact Or.inr hxy | exact Or.inr hxy.symm |
      exact (hchord (by simp [Sym2.eq_swap])).elim

section Layers

variable (G) (o : V)

private abbrev Tail (k : ℕ) : Set V := {x | k ≤ G.dist o x}
private abbrev Component (k : ℕ) := (G.induce (Tail G o k)).ConnectedComponent

private abbrev componentOf (k : ℕ) (x : V) (hx : k ≤ G.dist o x) :
    Component G o k :=
  (G.induce (Tail G o k)).connectedComponentMk ⟨x, hx⟩

private def parent {k : ℕ} (C : Component G o (k + 1)) : Component G o k :=
  C.map (G.induceHomOfLE (s := Tail G o (k + 1)) (s' := Tail G o k)
    (fun _ h => Nat.le_of_succ_le h)).toHom

private theorem parent_componentOf {k : ℕ} {x : V} (hx : k + 1 ≤ G.dist o x) :
    parent G o (componentOf G o (k + 1) x hx) =
      componentOf G o k x (Nat.le_of_succ_le hx) := rfl

private def Shadow {k : ℕ} (C : Component G o (k + 1)) : Set V :=
  {x | G.dist o x = k ∧ ∃ y : Tail G o (k + 1), y ∈ C.supp ∧ G.Adj x y.val}

variable {G o}

private theorem exists_predecessor {x : V} {k : ℕ} (hx : G.dist o x = k + 1) :
    ∃ y, G.Adj y x ∧ G.dist o y = k := by
  have hn : G.dist x o ≠ 0 := by rw [dist_comm, hx]; omega
  obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero hn
  cases p with
  | nil => simp at hx
  | @cons _ y _ h p =>
    have hd := length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p h)
    rw [dist_comm (G := G) (u := y) (v := o)] at hd
    rw [Walk.length_cons, dist_comm (G := G) (u := x) (v := o), hx] at hp
    exact ⟨y, h.symm, by omega⟩

private theorem walk_to_root (hconn : G.Connected) (x : V) :
    ∃ p : G.Walk x o, ∀ y ∈ p.support, G.dist o y ≤ G.dist o x := by
  generalize hx : G.dist o x = k
  induction k generalizing x with
  | zero =>
    have e := hconn.dist_eq_zero_iff.mp hx
    subst x
    exact ⟨.nil, by simp⟩
  | succ k ih =>
    obtain ⟨y, hyx, hy⟩ := exists_predecessor hx
    obtain ⟨p, hp⟩ := ih y hy
    refine ⟨.cons hyx.symm p, ?_⟩
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · omega
    · have := hp z hz
      omega

private theorem componentOf_adj {k : ℕ} {x y : V} (hx : k ≤ G.dist o x)
    (hy : k ≤ G.dist o y) (h : G.Adj x y) :
    componentOf G o k x hx = componentOf G o k y hy :=
  ConnectedComponent.connectedComponentMk_eq_of_adj (G := G.induce (Tail G o k)) h

private theorem component_meets_layer {k : ℕ} (C : Component G o k) :
    ∃ x : Tail G o k, x ∈ C.supp ∧ G.dist o x.val = k := by
  obtain ⟨x, hx⟩ := C.nonempty_supp
  generalize hd : G.dist o x.val = n
  induction n generalizing x with
  | zero =>
    have h := x.property
    exact ⟨x, hx, by change k ≤ G.dist o x.val at h; omega⟩
  | succ n ih =>
    by_cases he : n + 1 = k
    · exact ⟨x, hx, hd.trans he⟩
    obtain ⟨y, hyx, hy⟩ := exists_predecessor hd
    have hk := x.property
    change k ≤ G.dist o x.val at hk
    let y' : Tail G o k := ⟨y, by change k ≤ G.dist o y; omega⟩
    have hy' : y' ∈ C.supp := (C.mem_supp_congr_adj (v := y') (w := x) hyx).mpr hx
    exact ih y' hy' hy

private theorem shadow_nonempty {k : ℕ} (C : Component G o (k + 1)) :
    (Shadow G o C).Nonempty := by
  obtain ⟨x, hx, hlevel⟩ := component_meets_layer C
  obtain ⟨y, hyx, hy⟩ := exists_predecessor hlevel
  exact ⟨y, hy, x, hx, hyx⟩

private theorem mem_shadow_of_adj {k : ℕ} {x y : V} (hx : G.dist o x = k)
    (hy : k + 1 ≤ G.dist o y) (hxy : G.Adj x y) :
    x ∈ Shadow G o (componentOf G o (k + 1) y hy) :=
  ⟨hx, ⟨y, hy⟩, ConnectedComponent.connectedComponentMk_mem, hxy⟩

private theorem shadow_parent {k : ℕ} {C : Component G o (k + 1)} {x : V}
    (hx : x ∈ Shadow G o C) :
    parent G o C = componentOf G o k x hx.1.ge := by
  obtain ⟨y, hy, hxy⟩ := hx.2
  have e := (C.mem_supp_iff y).mp hy
  exact (congrArg (parent G o) e.symm).trans <|
    (parent_componentOf G o y.property).trans
      (componentOf_adj (Nat.le_of_succ_le y.property) hx.1.ge hxy.symm)

private theorem shadow_clique (hG : G.IsChordal) (hconn : G.Connected)
    {k : ℕ} (C : Component G o (k + 1)) : G.IsClique (Shadow G o C) := by
  intro x hx y hy hxy
  by_contra hn
  obtain ⟨hxk, x', hx', hxx'⟩ := hx
  obtain ⟨hyk, y', hy', hyy'⟩ := hy
  have hk : 0 < k := by
    by_contra! h
    have h₀ : k = 0 := by omega
    exact hxy ((hconn.dist_eq_zero_iff.mp (hxk.trans h₀)).symm.trans
      (hconn.dist_eq_zero_iff.mp (hyk.trans h₀)))
  let S : Set V := {z | z = x ∨ z = y ∨ ∃ z' ∈ C.supp, (z' : V) = z}
  let T : Set V := {z | z = x ∨ z = y ∨ G.dist o z < k}
  let mapToS : (G.induce (Tail G o (k + 1))).induce C.supp →g G.induce S :=
    { toFun := fun z => ⟨z.val.val, Or.inr (Or.inr ⟨z.val, z.property, rfl⟩)⟩
      map_rel' := fun h => h }
  have hc : (G.induce S).Reachable (mapToS ⟨x', hx'⟩) (mapToS ⟨y', hy'⟩) :=
    ((C.connected_toSimpleGraph).preconnected ⟨x', hx'⟩ ⟨y', hy'⟩).map mapToS
  have hs : (G.induce S).Reachable ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩ :=
    (show (G.induce S).Adj ⟨x, Or.inl rfl⟩ (mapToS ⟨x', hx'⟩) from hxx').reachable.trans
      (hc.trans (show (G.induce S).Adj (mapToS ⟨y', hy'⟩) ⟨y, Or.inr (Or.inl rfl)⟩
        from hyy'.symm).reachable)
  have low (z : V) (hz : G.dist o z = k) (hzT : z ∈ T) :
      (G.induce T).Reachable ⟨z, hzT⟩ ⟨o, Or.inr (Or.inr (by simpa using hk))⟩ := by
    have hz' : G.dist o z = k - 1 + 1 := by omega
    obtain ⟨w, hwz, hw⟩ := exists_predecessor hz'
    obtain ⟨p, hp⟩ := walk_to_root (o := o) hconn w
    have hsupp : ∀ a ∈ (p.cons hwz.symm).support, a ∈ T := by
      intro a ha
      rw [Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hzT
      · have := hp a ha
        exact Or.inr (Or.inr (by omega))
    exact (Walk.induce T (p.cons hwz.symm) hsupp).reachable
  apply separated_paths hG hxy hn hs
    ((low x hxk (Or.inl rfl)).trans (low y hyk (Or.inr (Or.inl rfl))).symm)
  intro a ha b hb hax hay hbx hby
  have ⟨a', _, ha'⟩ := (ha.resolve_left hax).resolve_left hay
  have hb' := (hb.resolve_left hbx).resolve_left hby
  have ha'' : k + 1 ≤ G.dist o a := ha' ▸ a'.property
  change G.dist o b < k at hb'
  refine ⟨fun e => by rw [e] at ha''; omega, fun hadj => ?_⟩
  have := hadj.diff_dist_adj (u := o)
  omega

private theorem exists_shadow_anchor [Finite V] (hG : G.IsChordal) (hconn : G.Connected)
    {k : ℕ} (C : Component G o (k + 2)) :
    ∃ a ∈ Shadow G o (parent G o C), ∀ x ∈ Shadow G o C, G.Adj a x := by
  classical
  let := Fintype.ofFinite V
  let B (x : V) := Finset.univ.filter (fun a => a ∈ Shadow G o (parent G o C) ∧ G.Adj a x)
  have nonempty {x : V} (hx : x ∈ Shadow G o C) : (B x).Nonempty := by
    obtain ⟨a, hax, ha⟩ := exists_predecessor hx.1
    have hp := shadow_parent hx
    have ham := mem_shadow_of_adj ha hx.1.ge hax
    rw [← hp] at ham
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ham, hax⟩⟩
  have comparable {x y : V} (hx : x ∈ Shadow G o C) (hy : y ∈ Shadow G o C) :
      B x ⊆ B y ∨ B y ⊆ B x := by
    by_contra h
    obtain ⟨a, ha, hay⟩ := Finset.not_subset.mp (fun h' => h (Or.inl h'))
    obtain ⟨b, hb, hbx⟩ := Finset.not_subset.mp (fun h' => h (Or.inr h'))
    obtain ⟨ha', hax⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨hb', hby⟩ := (Finset.mem_filter.mp hb).2
    have hab := shadow_clique hG hconn _ ha' hb' (fun e => hay (e.symm ▸ hb))
    have hxy := shadow_clique hG hconn _ hx hy (fun e => hay (e ▸ ha))
    have hne (p q : V) (hp : p ∈ Shadow G o (parent G o C))
        (hq : q ∈ Shadow G o C) : p ≠ q := by
      intro e
      have h₁ := hp.1
      have h₂ := hq.1
      rw [e] at h₁
      omega
    rcases four_cycle_diagonal hG hax hxy hby.symm hab.symm (hne _ _ ha' hy)
        (hne _ _ hb' hx).symm with h | h
    · exact hay (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha', h⟩)
    · exact hbx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb', h.symm⟩)
  let X := Finset.univ.filter (fun x => x ∈ Shadow G o C)
  have hX : X.Nonempty := by
    obtain ⟨x, hx⟩ := shadow_nonempty C
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image X (fun x => (B x).card) hX
  have hx' := (Finset.mem_filter.mp hx).2
  obtain ⟨a, ha⟩ := nonempty hx'
  refine ⟨a, (Finset.mem_filter.mp ha).2.1, fun y hy => ?_⟩
  have hsub : B x ⊆ B y := by
    rcases comparable hx' hy with h | h
    · exact h
    · have hcard := hmin y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
      exact (Finset.eq_of_subset_of_card_le h hcard).symm.subset
  exact (Finset.mem_filter.mp (hsub ha)).2.2

end Layers

section Gains

variable {H : Type v} [Group H]

private def gain [DecidableEq V] (g : V → V → H) (x y : V) : H :=
  if x = y then 1 else g x y

private theorem gain_adj [DecidableEq V] (g : V → V → H) {x y : V} (h : G.Adj x y) :
    gain g x y = g x y := ite_eq_right h.ne

variable [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

private theorem gain_triangle [DecidableEq V] {g : V → V → H} {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      Dist.dist (g i j * g j k) (g i k) ≤ ε)
    {a b c : V} (hab : a = b ∨ G.Adj a b) (hbc : b = c ∨ G.Adj b c)
    (hac : a = c ∨ G.Adj a c) :
    Dist.dist (gain g a b * gain g b c) (gain g a c) ≤ ε := by
  rcases hab with rfl | hab
  · simpa [gain] using hε
  rcases hbc with rfl | hbc
  · simpa [gain] using hε
  rcases hac with rfl | hac
  · simpa [gain, hab.ne, hab.ne.symm, hrev _ _ hab] using hε
  simpa only [gain_adj g hab, gain_adj g hbc, gain_adj g hac] using htri _ _ _ hab hbc hac

private theorem two_triangle_comparisons (γ : V → V → H) {a b c d : V} {ε : ℝ}
    (habc : Dist.dist (γ a b * γ b c) (γ a c) ≤ ε)
    (hbcd : Dist.dist (γ b c * γ c d) (γ b d) ≤ ε) :
    Dist.dist (γ a b * γ b d) (γ a c * γ c d) ≤ 2 * ε := by
  have h₁ : Dist.dist (γ a b * γ b d) (γ a b * (γ b c * γ c d)) ≤ ε := by
    rw [dist_mul_left, _root_.dist_comm]
    exact hbcd
  have h₂ : Dist.dist (γ a b * (γ b c * γ c d)) (γ a c * γ c d) ≤ ε := by
    rw [← mul_assoc, dist_mul_right]
    exact habc
  linarith [_root_.dist_triangle (γ a b * γ b d) (γ a b * (γ b c * γ c d)) (γ a c * γ c d)]

private def anchorGain {o : V} (γ : V → V → H) (a : (k : ℕ) → Component G o (k + 1) → V) :
    (k : ℕ) → Component G o (k + 1) → H
  | 0, _ => 1
  | k + 1, C => anchorGain γ a k (parent G o C) * γ (a k (parent G o C)) (a (k + 1) C)

private theorem exists_connected_uniform_potential [Finite V] (hG : G.IsChordal)
    (hconn : G.Connected) (o : V) (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      Dist.dist (g i j * g j k) (g i k) ≤ ε) :
    ∃ φ : V → H, ∀ x y, G.Adj x y → Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ 4 * ε := by
  classical
  let γ := gain g
  have tri {x y z : V} (hxy : x = y ∨ G.Adj x y) (hyz : y = z ∨ G.Adj y z)
      (hxz : x = z ∨ G.Adj x z) : Dist.dist (γ x y * γ y z) (γ x z) ≤ ε :=
    gain_triangle hε hrev htri hxy hyz hxz
  have near {k : ℕ} {C : Component G o (k + 1)} {x y : V}
      (hx : x ∈ Shadow G o C) (hy : y ∈ Shadow G o C) : x = y ∨ G.Adj x y :=
    (eq_or_ne x y).imp_right (shadow_clique hG hconn C hx hy)
  have exPred : ∀ x : V, 0 < G.dist o x →
      ∃ b, G.Adj b x ∧ G.dist o b + 1 = G.dist o x := by
    intro x hx
    have hx' : G.dist o x = G.dist o x - 1 + 1 := by omega
    obtain ⟨b, hb, hl⟩ := exists_predecessor hx'
    exact ⟨b, hb, by omega⟩
  choose b hb hbLevel using exPred
  have exAnchor : ∀ (k : ℕ) (C : Component G o (k + 2)),
      ∃ a ∈ Shadow G o (parent G o C), ∀ x ∈ Shadow G o C, G.Adj a x :=
    fun _ C => exists_shadow_anchor hG hconn C
  choose anchor anchor_parent anchor_adj using exAnchor
  let a : (k : ℕ) → Component G o (k + 1) → V
    | 0, _ => o
    | k + 1, C => anchor k C
  have a_adj {k : ℕ} {C : Component G o (k + 1)} {x : V} (hx : x ∈ Shadow G o C) :
      a k C = x ∨ G.Adj (a k C) x := by
    cases k with
    | zero => exact Or.inl (hconn.dist_eq_zero_iff.mp hx.1)
    | succ k => exact Or.inr (anchor_adj k C x hx)
  let Q := anchorGain γ a
  let atLevel (x : V) : (k : ℕ) → G.dist o x = k → H
    | 0, _ => 1
    | k + 1, hx =>
      let C := componentOf G o (k + 1) x hx.ge
      let p := b x (by omega)
      Q k C * (γ (a k C) p * γ p x)
  let φ : V → H := fun x => atLevel x (G.dist o x) rfl
  have atLevel_eq (x : V) (k : ℕ) (hx : G.dist o x = k) : φ x = atLevel x k hx := by
    subst k
    rfl
  have φ_eval {x : V} {k : ℕ} (hx : G.dist o x = k + 1) :
      let C := componentOf G o (k + 1) x hx.ge
      let p := b x (by omega)
      φ x = Q k C * (γ (a k C) p * γ p x) :=
    atLevel_eq x (k + 1) hx
  have b_shadow {x : V} {k : ℕ} (hx : G.dist o x = k + 1) :
      b x (by omega) ∈ Shadow G o (componentOf G o (k + 1) x hx.ge) := by
    have hs := hbLevel x (by omega)
    exact mem_shadow_of_adj (by omega) hx.ge (hb x (by omega))
  have across {x y : V} {k : ℕ} (hx : G.dist o x = k) (hy : G.dist o y = k + 1)
      (hxy : G.Adj x y) : Dist.dist (φ x * γ x y) (φ y) ≤ 4 * ε := by
    cases k with
    | zero =>
      have he := hconn.dist_eq_zero_iff.mp hx
      subst x
      have bp : b y (by omega) = o := hconn.dist_eq_zero_iff.mp (b_shadow hy).1 |>.symm
      have hroot : φ o = 1 := atLevel_eq o 0 (by simp)
      rw [hroot, φ_eval hy]
      simpa [Q, anchorGain, a, γ, gain, bp, hxy.ne] using (show 0 ≤ 4 * ε by linarith)
    | succ k =>
      let C := componentOf G o (k + 2) y hy.ge
      have xs : x ∈ Shadow G o C := mem_shadow_of_adj hx hy.ge hxy
      have hp : parent G o C = componentOf G o (k + 1) x hx.ge := shadow_parent xs
      let p := b x (by omega)
      let q := b y (by omega)
      have ps : p ∈ Shadow G o (parent G o C) := hp ▸ b_shadow hx
      have qs : q ∈ Shadow G o C := b_shadow hy
      have as : a (k + 1) C ∈ Shadow G o (parent G o C) := anchor_parent k C
      have ha : G.Adj (a (k + 1) C) x := anchor_adj k C x xs
      let m := Q (k + 1) C * γ (a (k + 1) C) x
      have h₁ : Dist.dist (φ x) m ≤ 2 * ε := by
        rw [φ_eval hx, ← hp]
        change Dist.dist (Q k (parent G o C) * (γ (a k (parent G o C)) p * γ p x))
          ((Q k (parent G o C) * γ (a k (parent G o C)) (a (k + 1) C)) *
            γ (a (k + 1) C) x) ≤ 2 * ε
        rw [mul_assoc (Q k (parent G o C)), dist_mul_left]
        exact two_triangle_comparisons γ (tri (a_adj ps) (near ps as) (a_adj as))
          (tri (near ps as) (Or.inr ha) (Or.inr (hb x (by omega))))
      have h₂ : Dist.dist (m * γ x y) (φ y) ≤ 2 * ε := by
        rw [φ_eval hy]
        change Dist.dist ((Q (k + 1) C * γ (a (k + 1) C) x) * γ x y)
          (Q (k + 1) C * (γ (a (k + 1) C) q * γ q y)) ≤ 2 * ε
        rw [mul_assoc, dist_mul_left]
        exact two_triangle_comparisons γ (tri (Or.inr ha) (near xs qs) (a_adj qs))
          (tri (near xs qs) (Or.inr (hb y (by omega))) (Or.inr hxy))
      have h₁' : Dist.dist (φ x * γ x y) (m * γ x y) ≤ 2 * ε := by rwa [dist_mul_right]
      linarith [_root_.dist_triangle (φ x * γ x y) (m * γ x y) (φ y)]

  have within {x y : V} {k : ℕ} (hx : G.dist o x = k + 1) (hy : G.dist o y = k + 1)
      (hxy : G.Adj x y) : Dist.dist (φ x * γ x y) (φ y) ≤ 4 * ε := by
    let C := componentOf G o (k + 1) x hx.ge
    have hc : C = componentOf G o (k + 1) y hy.ge := componentOf_adj hx.ge hy.ge hxy
    let p := b x (by omega)
    let q := b y (by omega)
    have ps : p ∈ Shadow G o C := b_shadow hx
    have qs : q ∈ Shadow G o C := hc.symm ▸ b_shadow hy
    have hpx : G.Adj p x := hb x (by omega)
    have hqy : G.Adj q y := hb y (by omega)
    have hpy (h : G.Adj p y) : Dist.dist ((γ (a k C) p * γ p x) * γ x y)
        (γ (a k C) p * γ p y) ≤ ε := by
      rw [mul_assoc, dist_mul_left]
      exact tri (Or.inr hpx) (Or.inr hxy) (Or.inr h)
    have hbound : Dist.dist ((γ (a k C) p * γ p x) * γ x y)
        (γ (a k C) q * γ q y) ≤ 3 * ε := by
      by_cases he : p = q
      · simpa only [he] using (hpy (he ▸ hqy)).trans (show ε ≤ 3 * ε by linarith)
      have hpq := shadow_clique hG hconn C ps qs he
      have hne (w z : V) (hw : G.dist o w = k) (hz : G.dist o z = k + 1) : w ≠ z := by
        intro e
        rw [e] at hw
        omega
      rcases four_cycle_diagonal hG hpx hxy hqy.symm hpq.symm (hne p y ps.1 hy)
          (hne q x qs.1 hx).symm with h | h
      · have h₂ := two_triangle_comparisons γ (tri (a_adj ps) (Or.inr hpq) (a_adj qs))
          (tri (Or.inr hpq) (Or.inr hqy) (Or.inr h))
        linarith [_root_.dist_triangle ((γ (a k C) p * γ p x) * γ x y)
          (γ (a k C) p * γ p y) (γ (a k C) q * γ q y), hpy h]
      · have h₁ : Dist.dist ((γ (a k C) p * γ p x) * γ x y)
            ((γ (a k C) p * γ p x) * (γ x q * γ q y)) ≤ ε := by
          rw [dist_mul_left, _root_.dist_comm]
          exact tri (Or.inr h) (Or.inr hqy) (Or.inr hxy)
        have h₂ : Dist.dist ((γ (a k C) p * γ p x) * (γ x q * γ q y))
            ((γ (a k C) p * γ p q) * γ q y) ≤ ε := by
          simpa only [mul_assoc, dist_mul_left] using
            (show Dist.dist ((γ p x * γ x q) * γ q y) (γ p q * γ q y) ≤ ε by
              rw [dist_mul_right]
              exact tri (Or.inr hpx) (Or.inr h) (Or.inr hpq))
        have h₃ : Dist.dist ((γ (a k C) p * γ p q) * γ q y) (γ (a k C) q * γ q y) ≤ ε := by
          rw [dist_mul_right]
          exact tri (a_adj ps) (Or.inr hpq) (a_adj qs)
        linarith [
          _root_.dist_triangle ((γ (a k C) p * γ p x) * γ x y)
            ((γ (a k C) p * γ p x) * (γ x q * γ q y)) (γ (a k C) q * γ q y),
          _root_.dist_triangle ((γ (a k C) p * γ p x) * (γ x q * γ q y))
            ((γ (a k C) p * γ p q) * γ q y) (γ (a k C) q * γ q y)]
    rw [φ_eval hx, φ_eval hy, ← hc]
    change Dist.dist ((Q k C * (γ (a k C) p * γ p x)) * γ x y)
      (Q k C * (γ (a k C) q * γ q y)) ≤ 4 * ε
    rw [mul_assoc (Q k C), dist_mul_left]
    exact hbound.trans (by linarith)
  have forward {x y : V} (hxy : G.Adj x y) (h : G.dist o x ≤ G.dist o y) :
      Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ 4 * ε := by
    rw [← dist_mul_left (φ x), ← mul_assoc, mul_inv_cancel, one_mul, ← gain_adj g hxy]
    rcases hxy.diff_dist_adj (u := o) with he | he | he
    · cases hk : G.dist o x with
      | zero =>
        exact (hxy.ne ((hconn.dist_eq_zero_iff.mp hk).symm.trans
          (hconn.dist_eq_zero_iff.mp (he.trans hk)))).elim
      | succ k => exact within hk (he.trans hk) hxy
    · exact across rfl he hxy
    · have he' : G.dist o y = G.dist o x := by omega
      cases hk : G.dist o x with
      | zero =>
        exact (hxy.ne ((hconn.dist_eq_zero_iff.mp hk).symm.trans
          (hconn.dist_eq_zero_iff.mp (he'.trans hk)))).elim
      | succ k => exact within hk (he'.trans hk) hxy
  refine ⟨φ, fun x y hxy => ?_⟩
  rcases le_total (G.dist o x) (G.dist o y) with h | h
  · exact forward hxy h
  · rw [hrev y x hxy.symm]
    simpa only [mul_inv_rev, inv_inv] using
      (dist_inv_inv (g y x) ((φ y)⁻¹ * φ x)).le.trans (forward hxy.symm h)

/-- Triangle defects of at most ε give simultaneous edge errors of at most 4ε on a finite
chordal graph. The pseudometric is invariant under left and right multiplication. -/
theorem IsChordal.exists_uniform_approximate_gain_potential
    [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      Dist.dist (g i j * g j k) (g i k) ≤ ε) :
    ∃ φ : V → H, ∀ i j, G.Adj i j →
      Dist.dist (g i j) ((φ i)⁻¹ * φ j) ≤ 4 * ε := by
  classical
  have hcomp (c : G.ConnectedComponent) :
      ∃ ψ : c → H, ∀ i j, c.toSimpleGraph.Adj i j →
        Dist.dist (g i.val j.val) ((ψ i)⁻¹ * ψ j) ≤ 4 * ε := by
    obtain ⟨o, ho⟩ := c.nonempty_supp
    exact exists_connected_uniform_potential (hG.induce c.supp) c.connected_toSimpleGraph ⟨o, ho⟩
      (fun i j => g i.val j.val) ε hε (fun i j => hrev i.val j.val)
      (fun i j k => htri i.val j.val k.val)
  choose ψ hψ using hcomp
  let φ (i : V) := ψ (G.connectedComponentMk i) ⟨i, ConnectedComponent.connectedComponentMk_mem⟩
  have φ_eq (i : V) (c : G.ConnectedComponent) (hi : G.connectedComponentMk i = c) :
      φ i = ψ c ⟨i, hi⟩ := by
    subst c
    rfl
  refine ⟨φ, fun i j hij => ?_⟩
  have hj := ConnectedComponent.connectedComponentMk_eq_of_adj hij.symm
  rw [φ_eq j _ hj]
  exact hψ (G.connectedComponentMk i) ⟨i, rfl⟩ ⟨j, hj⟩ hij

end Gains

end SimpleGraph
