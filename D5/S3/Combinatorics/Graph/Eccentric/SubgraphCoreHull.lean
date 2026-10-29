/- GID: D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreHull
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Eccentric/SubgraphCoreHull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A set unseparated by vertex deletion has a connected cover without cut vertices. -/
import D5.S3.Combinatorics.Graph.Eccentric.DePatraBridge
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Combinatorics.Graph.Eccentric.SubgraphCoreHull
open SimpleGraph DePatraBridge Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V}

private def hull (G : SimpleGraph V) (S : Set V) : Set V :=
  {x | ∃ a ∈ S, ∃ b ∈ S, ∃ p : G.Walk a b, p.IsPath ∧ x ∈ p.support}

private lemma mem_hull {S : Set V} {x : V} (hx : x ∈ S) : x ∈ hull G S :=
  ⟨x, hx, x, hx, .nil, by simp, by simp⟩

private lemma path_hull {S : Set V} {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (p : G.Walk a b) (hp : p.IsPath) : ∀ x ∈ p.support, x ∈ hull G S :=
  fun x hx => ⟨a, ha, b, hb, p, hp, hx⟩

private lemma walk_le_induced {S : Set V} {a b : V} (p : G.Walk a b)
    (hs : ∀ x ∈ p.support, x ∈ S) : p.toSubgraph ≤ (⊤ : G.Subgraph).induce S := by
  constructor
  · intro x hx
    exact hs x ((Walk.mem_verts_toSubgraph _).mp hx)
  · intro x y hxy
    exact ⟨hs x ((Walk.mem_verts_toSubgraph _).mp hxy.fst_mem),
      hs y ((Walk.mem_verts_toSubgraph _).mp hxy.snd_mem), p.toSubgraph.adj_sub hxy⟩

private lemma endpoint_avoiding {a b x z : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ p.support) (hxz : x ≠ z) :
    ∃ s, (s = a ∨ s = b) ∧ ∃ q : G.Walk x s,
      ∀ w ∈ q.support, w ∈ p.support ∧ w ≠ z := by
  let l := p.takeUntil x hx
  let t := p.dropUntil x hx
  by_cases hz : z ∈ l.support
  · have hd : l.support.Disjoint t.support.tail := by
      apply ((Walk.isPath_append l t).mp ?_).2.2
      simpa only [l, t, Walk.take_spec] using hp
    have hzt : z ∉ t.support := by
      intro hzt
      rcases (Walk.mem_support_iff t).mp hzt with he | he
      · exact hxz he.symm
      · have hn : ∀ u ∈ l.support, ∀ v ∈ t.support.tail, u ≠ v := by
          simpa only [List.disjoint_iff_ne] using hd
        exact hn z hz z he rfl
    refine ⟨b, Or.inr rfl, t, ?_⟩
    intro w hw
    exact ⟨p.support_dropUntil_subset_support hx hw, fun he => hzt (he ▸ hw)⟩
  · refine ⟨a, Or.inl rfl, l.reverse, ?_⟩
    intro w hw
    have hw' : w ∈ l.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hw
    exact ⟨p.support_takeUntil_subset_support hx hw', fun he => hz (he ▸ hw')⟩

private lemma hull_connected (hG : G.Connected) {S : Set V} (hS : S.Nonempty) :
    ((⊤ : G.Subgraph).induce (hull G S)).Connected := by
  obtain ⟨a, ha⟩ := hS
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  refine ⟨⟨a, mem_hull ha⟩, ?_⟩
  intro u v hu hv
  obtain ⟨b, hb, c, hc, p, hp, hup⟩ := hu
  obtain ⟨d, hd, e, he, q, hq, hvq⟩ := hv
  obtain ⟨m, hm⟩ := hG.exists_isPath b d
  let pu := (p.takeUntil u hup).reverse
  let pv := q.takeUntil v hvq
  refine ⟨pu.append (m.append pv), walk_le_induced _ ?_⟩
  intro w hw
  simp only [Walk.mem_support_append_iff] at hw
  rcases hw with hw | hw | hw
  · have hw' : w ∈ (p.takeUntil u hup).support := by
      simpa only [pu, Walk.support_reverse, List.mem_reverse] using hw
    exact path_hull hb hc p hp w (p.support_takeUntil_subset_support hup hw')
  · exact path_hull hb hd m hm w hw
  · exact path_hull hd he q hq w (q.support_takeUntil_subset_support hvq hw)

/-- Inseparability under vertex deletion supplies one connected subgraph with no cut vertex.
The statement includes singleton sets and empty deletion. -/
theorem exists_no_cut_cover (hG : G.Connected) (S : Set V) (hS : S.Nonempty)
    (hsep : ∀ (z u v : V) (hu : u ≠ z) (hv : v ≠ z), u ∈ S → v ∈ S →
      (G.induce ({z}ᶜ : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    ∃ H : G.Subgraph, H.Connected ∧ S ⊆ H.verts ∧
      ∀ z : V, (restrict H ({z}ᶜ : Set V)).Preconnected := by
  let H := (⊤ : G.Subgraph).induce (hull G S)
  refine ⟨H, hull_connected hG hS, fun _ hx => mem_hull hx, ?_⟩
  intro z
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
  intro u v hu hv
  have huH : u ∈ hull G S := hu.1
  have hvH : v ∈ hull G S := hv.1
  have huz : u ≠ z := by simpa using hu.2
  have hvz : v ≠ z := by simpa using hv.2
  obtain ⟨a, ha, b, hb, p, hp, hup⟩ := huH
  obtain ⟨c, hc, d, hd, q, hq, hvq⟩ := hvH
  obtain ⟨s, hs, ps, hps⟩ := endpoint_avoiding p hp hup huz
  obtain ⟨t, ht, pt, hpt⟩ := endpoint_avoiding q hq hvq hvz
  have hsS : s ∈ S := hs.elim (fun he => he ▸ ha) (fun he => he ▸ hb)
  have htS : t ∈ S := ht.elim (fun he => he ▸ hc) (fun he => he ▸ hd)
  have hsz : s ≠ z := (hps s ps.end_mem_support).2
  have htz : t ≠ z := (hpt t pt.end_mem_support).2
  obtain ⟨m, hm⟩ := (hsep z s t hsz htz hsS htS).exists_isPath
  let emb := (SimpleGraph.Embedding.induce (G := G) ({z}ᶜ : Set V)).toHom
  let n := m.map emb
  have hn : n.IsPath := hm.map (by exact Subtype.val_injective)
  have hnH : ∀ w ∈ n.support, w ∈ hull G S ∧ w ≠ z := by
    intro w hw
    refine ⟨path_hull hsS htS n hn w hw, ?_⟩
    rw [Walk.support_map, List.mem_map] at hw
    obtain ⟨w', _, he⟩ := hw
    change w'.val = w at he
    exact he ▸ w'.property
  let k := ps.append (n.append pt.reverse)
  have hk : ∀ w ∈ k.support, w ∈ hull G S ∧ w ≠ z := by
    intro w hw
    change w ∈ (ps.append (n.append pt.reverse)).support at hw
    have hh := (Walk.mem_support_append_iff ps (n.append pt.reverse)).mp hw
    rcases hh with hw | hw
    · exact ⟨path_hull ha hb p hp w (hps w hw).1, (hps w hw).2⟩
    have hh := (Walk.mem_support_append_iff n pt.reverse).mp hw
    rcases hh with hw | hw
    · exact hnH w hw
    · have hw' : w ∈ pt.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hw
      exact ⟨path_hull hc hd q hq w (hpt w hw').1, (hpt w hw').2⟩
  refine ⟨k, ?_⟩
  constructor
  · intro w hw
    exact ⟨(hk w ((Walk.mem_verts_toSubgraph _).mp hw)).1,
      (hk w ((Walk.mem_verts_toSubgraph _).mp hw)).2⟩
  · intro a b hab
    have ha := hk a ((Walk.mem_verts_toSubgraph _).mp hab.fst_mem)
    have hb := hk b ((Walk.mem_verts_toSubgraph _).mp hab.snd_mem)
    exact ⟨ha, hb, ha.1, hb.1, k.toSubgraph.adj_sub hab⟩

end
end D5.S3.Combinatorics.Graph.Eccentric.SubgraphCoreHull
