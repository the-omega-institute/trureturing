/- GID: D5/S3/Combinatorics/Graph/DirectedForestGluingSigns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectedForestGluingSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.Order.Interval.Finset.Fin]
   utility: none
   digest: Actual directed forest gluing and lawful reattachment determine ascending matching signs. -/
import D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Graph.DirectedForestGluingSigns
open SimpleGraph
set_option maxHeartbeats 1200000 in
open Classical in
theorem directed_forest_gluing_signs (n : ℕ) :
    let Lawful := fun (U W : Finset (Fin n)) (F : Finset (Fin n × Fin n)) =>
      (∀ e ∈ F, e.1 ≠ e.2) ∧
      (∀ e ∈ F, (e.2, e.1) ∉ F) ∧
      (fromRel (fun x y => (x, y) ∈ F)).IsAcyclic ∧
      (∀ v, ∃! u, u ∈ U ∧ (fromRel (fun x y => (x, y) ∈ F)).Reachable v u) ∧
      (∀ v, ∃! w, w ∈ W ∧ (fromRel (fun x y => (x, y) ∈ F)).Reachable v w) ∧
      (∀ x y, (x, y) ∈ F → ∀ u ∈ U,
        (fromRel (fun x y => (x, y) ∈ F)).Reachable u x →
        (fromRel (fun x y => (x, y) ∈ F)).dist u x <
        (fromRel (fun x y => (x, y) ∈ F)).dist u y)
    ∃ μ : (k : ℕ) → (U W : Finset (Fin n)) → U.card = k → W.card = k →
      (F : Finset (Fin n × Fin n)) → Lawful U W F → Equiv.Perm (Fin k),
    let ε := fun (k : ℕ) (U W : Finset (Fin n)) (hU : U.card = k) (hW : W.card = k)
      (F : Finset (Fin n × Fin n)) (hF : Lawful U W F) =>
      (-1 : ℤ) ^ (n + k + (∑ u ∈ U, u.val) + (∑ w ∈ W, w.val)) *
        (Equiv.Perm.sign (μ k U W hU hW F hF) : ℤ)
    (∀ (k : ℕ) (U W : Finset (Fin n)) (hU : U.card = k) (hW : W.card = k)
      (F : Finset (Fin n × Fin n)) (hF : Lawful U W F) (a : Fin k),
      (fromRel (fun x y => (x, y) ∈ F)).Reachable
      (U.orderEmbOfFin hU a) (W.orderEmbOfFin hW (μ k U W hU hW F hF a))) ∧
    (∃ hEmpty : Lawful Finset.univ Finset.univ (∅ : Finset (Fin n × Fin n)),
      ε n Finset.univ Finset.univ (by simp) (by simp) ∅ hEmpty = 1) ∧
    (∀ (k : ℕ), 1 ≤ k → ∀ (U W : Finset (Fin n)) (hU : U.card = k) (hW : W.card = k)
      (w₀ i j : Fin n) (_hw₀ : w₀ ∈ W) (hi : i ∉ W) (hj : j ∉ U),
      ∀ (F : Finset (Fin n × Fin n)) (hF : Lawful (insert j U) (insert i W) F),
      let H := if Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i
        then insert (w₀, j) F else insert (i, j) F
      ∃ hH : Lawful U W H,
        (-1 : ℤ) ^ (i.val + (W.filter (· < i)).card + j.val + (U.filter (· < j)).card) *
          ε (k + 1) (insert j U) (insert i W)
            (by rw [Finset.card_insert_of_notMem hj, hU])
            (by rw [Finset.card_insert_of_notMem hi, hW]) F hF =
        (if Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i then -1 else 1) *
          ε k U W hU hW H hH) ∧
    (∀ (k : ℕ), 1 ≤ k → ∀ (U W : Finset (Fin n)) (hU : U.card = k) (hW : W.card = k)
      (i j w₀ : Fin n), w₀ ∈ W → ∀ (F : Finset (Fin n × Fin n))
      (hF : Lawful U W F) (hF' : Lawful U W (insert (w₀, j) (F.erase (i, j)))),
      ε k U W hU hW F hF = ε k U W hU hW (insert (w₀, j) (F.erase (i, j))) hF') := by
  classical
  let Lawful (U W : Finset (Fin n)) (F : Finset ((Fin n) × (Fin n))) : Prop :=
    (∀ e ∈ F, e.1 ≠ e.2) ∧
    (∀ e ∈ F, (e.2, e.1) ∉ F) ∧
    (fromRel (fun x y => (x, y) ∈ F)).IsAcyclic ∧
    (∀ v, ∃! u, u ∈ U ∧ (fromRel (fun x y => (x, y) ∈ F)).Reachable v u) ∧
    (∀ v, ∃! w, w ∈ W ∧ (fromRel (fun x y => (x, y) ∈ F)).Reachable v w) ∧
    (∀ x y, (x, y) ∈ F → ∀ u ∈ U,
      (fromRel (fun x y => (x, y) ∈ F)).Reachable u x →
      (fromRel (fun x y => (x, y) ∈ F)).dist u x <
      (fromRel (fun x y => (x, y) ∈ F)).dist u y)
  
  have rooted_directed_reachability (E : (Fin n) → (Fin n) → Prop)
      (hloop : ∀ x, ¬ E x x) (u : (Fin n))
      (haway : ∀ x y, E x y → (fromRel E).Reachable u x →
        (fromRel E).dist u x < (fromRel E).dist u y) (v : (Fin n)) :
      Relation.ReflTransGen E u v ↔ (fromRel E).Reachable u v := by
    let G := fromRel E
    constructor
    · intro h
      induction h with
      | refl => exact Reachable.refl _
      | @tail x y hxy he ih =>
        exact ih.trans (show G.Adj x y from ⟨fun h => hloop x (h ▸ he), Or.inl he⟩).reachable
    · have descent : ∀ m v, G.dist u v = m → G.Reachable u v →
          Relation.ReflTransGen E u v := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ih =>
          intro v hdist hreach
          by_cases huv : u = v
          · subst v
            exact Relation.ReflTransGen.refl
          obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
          have hn : ¬p.Nil := Walk.not_nil_of_ne huv
          have hstep := p.adj_penultimate hn
          have hd := dist_le p.dropLast
          have hl := p.length_dropLast_add_one hn
          have hlt : G.dist u p.penultimate < m := by omega
          have he : E p.penultimate v := by
            rcases hstep with ⟨_, he | he⟩
            · exact he
            · have hrev := haway v p.penultimate he hreach
              dsimp [G] at hlt hdist
              omega
          exact (ih _ hlt _ rfl p.dropLast.reachable).tail he
      intro hreach
      exact descent _ _ rfl hreach
  
  
  have bridge_reachable_profile (G : SimpleGraph (Fin n))
      (t j : (Fin n)) (hne : t ≠ j) (x y : (Fin n)) :
      (G ⊔ edge t j).Reachable x y ↔ G.Reachable x y ∨
        (G.Reachable x t ∧ G.Reachable j y) ∨
        (G.Reachable x j ∧ G.Reachable t y) := by
    constructor
    · rintro ⟨p⟩
      induction p with
      | nil => exact Or.inl (Reachable.refl _)
      | @cons a b c hab p ih =>
        rcases hab with hab | hab
        · rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inl (hab.reachable.trans h)
          · exact Or.inr (Or.inl ⟨hab.reachable.trans h₁, h₂⟩)
          · exact Or.inr (Or.inr ⟨hab.reachable.trans h₁, h₂⟩)
        · rcases (edge_adj t j a b).mp hab with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
          · rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · exact Or.inr (Or.inl ⟨Reachable.refl _, h⟩)
            · exact Or.inl (h₁.symm.trans h₂)
            · exact Or.inl h₂
          · rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · exact Or.inr (Or.inr ⟨Reachable.refl _, h⟩)
            · exact Or.inl h₂
            · exact Or.inl (h₁.symm.trans h₂)
    · have he : (G ⊔ edge t j).Reachable t j :=
        (show (G ⊔ edge t j).Adj t j from
          Or.inr ((edge_adj t j t j).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)).reachable
      rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · exact h.mono le_sup_left
      · exact (h₁.mono le_sup_left).trans (he.trans (h₂.mono le_sup_left))
      · exact (h₁.mono le_sup_left).trans (he.symm.trans (h₂.mono le_sup_left))
  
  
  have acyclic_path_length {G : SimpleGraph (Fin n)}
      (hG : G.IsAcyclic) {x y : (Fin n)} (p : G.Walk x y) (hp : p.IsPath) :
      p.length = G.dist x y := by
    obtain ⟨q, hq, hlen⟩ := p.reachable.exists_path_of_dist
    have heq := (hG.subsingleton_path x y).elim (⟨p, hp⟩ : G.Path x y) ⟨q, hq⟩
    have heq' := congrArg (fun r : G.Path x y => r.val.length) heq
    exact heq'.trans hlen
  
  have bridge_old_distance (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
      (t j : (Fin n)) (hsep : ¬G.Reachable t j) {x y : (Fin n)} (hxy : G.Reachable x y) :
      (G ⊔ edge t j).dist x y = G.dist x y := by
    obtain ⟨p, hp, hlen⟩ := hxy.exists_path_of_dist
    have ha := hG.sup_edge_of_not_reachable hsep
    have hm := hp.mapLe (le_sup_left : G ≤ G ⊔ edge t j)
    have hd := acyclic_path_length ha (p.mapLe le_sup_left) hm
    simpa only [Walk.length_mapLe, hlen] using hd.symm
  
  have bridge_cross_distance (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
      (t j : (Fin n)) (hsep : ¬G.Reachable t j) {x y : (Fin n)}
      (hxt : G.Reachable x t) (hjy : G.Reachable j y) :
      (G ⊔ edge t j).dist x y = G.dist x t + 1 + G.dist j y := by
    have hne : t ≠ j := fun h => hsep (h ▸ Reachable.refl t)
    obtain ⟨p, hp, hplen⟩ := hxt.exists_path_of_dist
    obtain ⟨q, hq, hqlen⟩ := hjy.exists_path_of_dist
    let H := G ⊔ edge t j
    have hle : G ≤ H := le_sup_left
    have he : H.Adj t j :=
      Or.inr ((edge_adj t j t j).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
    let r := (p.mapLe hle).append (Walk.cons he (q.mapLe hle))
    have hdis : p.support.Disjoint q.support := by
      intro z hz₁ hz₂
      obtain ⟨_, p₂, _⟩ := p.mem_support_iff_exists_append.mp hz₁
      obtain ⟨q₁, _, _⟩ := q.mem_support_iff_exists_append.mp hz₂
      have htz : G.Reachable t z := p₂.reachable.symm
      have hjz : G.Reachable j z := q₁.reachable
      exact hsep (htz.trans hjz.symm)
    have hr : r.IsPath := by
      rw [Walk.isPath_def]
      dsimp [r]
      simp only [Walk.support_append, Walk.support_cons, List.tail_cons,
        Walk.support_mapLe_eq_support]
      exact List.nodup_append'.mpr ⟨hp.support_nodup, hq.support_nodup, hdis⟩
    have hd := acyclic_path_length (hG.sup_edge_of_not_reachable hsep) r hr
    have hl : r.length = G.dist x t + 1 + G.dist j y := by
      simp only [r, Walk.length_append, Walk.length_cons, Walk.length_mapLe, hplen, hqlen]
      omega
    exact hd.symm.trans hl
  
  
  have bridge_remove_root (G : SimpleGraph (Fin n)) (A : (Fin n) → Prop)
      (hroots : ∀ v, ∃! u, A u ∧ G.Reachable v u)
      (t j removed : (Fin n)) (hj : A removed) (hjr : G.Reachable j removed)
      (hsep : ¬G.Reachable t j) :
      ∀ v, ∃! u, (A u ∧ u ≠ removed) ∧ (G ⊔ edge t j).Reachable v u := by
    have hne : t ≠ j := fun h => hsep (h ▸ Reachable.refl t)
    have hbad : ∀ u, A u → u ≠ removed → ¬G.Reachable j u := by
      intro u hu hneq hju
      exact hneq ((hroots j).unique ⟨hu, hju⟩ ⟨hj, hjr⟩)
    obtain ⟨r, hr, _⟩ := hroots t
    have hrj : r ≠ removed := by
      rintro rfl
      exact hsep (hr.2.trans hjr.symm)
    intro v
    by_cases hvj : G.Reachable v j
    · refine ⟨r, ⟨⟨hr.1, hrj⟩, ?_⟩, ?_⟩
      · exact (bridge_reachable_profile G t j hne v r).mpr (Or.inr (Or.inr ⟨hvj, hr.2⟩))
      · intro u hu
        rcases (bridge_reachable_profile G t j hne v u).mp hu.2 with h | ⟨_, h⟩ | ⟨_, h⟩
        · exact (hbad u hu.1.1 hu.1.2 (hvj.symm.trans h)).elim
        · exact (hbad u hu.1.1 hu.1.2 h).elim
        · exact (hroots t).unique ⟨hu.1.1, h⟩ hr
    · obtain ⟨s, hs, _⟩ := hroots v
      have hsj : s ≠ removed := by
        rintro rfl
        exact hvj (hs.2.trans hjr.symm)
      refine ⟨s, ⟨⟨hs.1, hsj⟩, hs.2.mono le_sup_left⟩, ?_⟩
      intro u hu
      rcases (bridge_reachable_profile G t j hne v u).mp hu.2 with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact (hroots v).unique ⟨hu.1.1, h⟩ hs
      · exact (hbad u hu.1.1 hu.1.2 h).elim
      · exact (hvj h).elim
  
  have literal_insert_graph (F : Finset ((Fin n) × (Fin n)))
      (t j : (Fin n)) :
      fromRel (fun x y => (x, y) ∈ insert (t, j) F) =
        fromRel (fun x y => (x, y) ∈ F) ⊔ edge t j := by
    ext x y
    simp only [fromRel_adj, Finset.mem_insert, Prod.mk.injEq, sup_adj, edge_adj]
    tauto
  
  
  have bridge_away_orientation (E : (Fin n) → (Fin n) → Prop)
      (A : (Fin n) → Prop) (hloop : ∀ x, ¬E x x)
      (hG : (fromRel E).IsAcyclic)
      (hroots : ∀ v, ∃! u, A u ∧ (fromRel E).Reachable v u)
      (haway : ∀ x y, E x y → ∀ u, A u → (fromRel E).Reachable u x →
        (fromRel E).dist u x < (fromRel E).dist u y)
      (t j : (Fin n)) (hj : A j) (hsep : ¬(fromRel E).Reachable t j)
      (x y : (Fin n)) (he : E x y ∨ (x = t ∧ y = j))
      (u : (Fin n)) (hu : A u) (huj : u ≠ j)
      (hux : (fromRel E ⊔ edge t j).Reachable u x) :
      (fromRel E ⊔ edge t j).dist u x < (fromRel E ⊔ edge t j).dist u y := by
    let G := fromRel E
    have hne : t ≠ j := fun h => hsep (h ▸ Reachable.refl t)
    have hnuj : ¬G.Reachable u j := by
      intro h
      exact huj ((hroots j).unique ⟨hu, h.symm⟩ ⟨hj, Reachable.refl _⟩)
    rcases he with he | hnew
    · have hxy : G.Adj x y := ⟨fun h => hloop x (h ▸ he), Or.inl he⟩
      rcases (bridge_reachable_profile G t j hne u x).mp hux with h | ⟨hut, hjx⟩ | ⟨huj', _⟩
      · rw [bridge_old_distance G hG t j hsep h,
          bridge_old_distance G hG t j hsep (h.trans hxy.reachable)]
        exact haway x y he u hu h
      · rw [bridge_cross_distance G hG t j hsep hut hjx,
          bridge_cross_distance G hG t j hsep hut (hjx.trans hxy.reachable)]
        have hjaway := haway x y he j hj hjx
        change G.dist j x < G.dist j y at hjaway
        omega
      · exact (hnuj huj').elim
    · rcases hnew with ⟨hx, hy⟩
      subst x
      subst y
      have hut : G.Reachable u t := by
        rcases (bridge_reachable_profile G t j hne u t).mp hux with h | ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact h
        · exact (hnuj h).elim
      rw [bridge_old_distance G hG t j hsep hut,
        bridge_cross_distance G hG t j hsep hut (Reachable.refl j)]
      simp
  
  
  have literal_glue_lawful
      (U W : Finset (Fin n)) (F : Finset ((Fin n) × (Fin n))) (i j w₀ : (Fin n))
      (hw₀ : w₀ ∈ W) (hi : i ∉ W) (hj : j ∉ U)
      (hF : Lawful (insert j U) (insert i W) F) :
      Lawful U W (if Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i
        then insert (w₀, j) F else insert (i, j) F) := by
    classical
    rcases hF with ⟨hloop, hanti, hacyc, hroots, hmarks, haway⟩
    let E := fun x y => (x, y) ∈ F
    let G := fromRel E
    have hL : ∀ x, ¬E x x := fun x he => hloop (x, x) he rfl
    have hAdj : ∀ x y, E x y → G.Adj x y :=
      fun x y he => ⟨hloop (x, y) he, Or.inl he⟩
    have hdir := rooted_directed_reachability E hL j
      (fun x y he hreach => haway x y he j (by simp) hreach) i
    have hUs : ∀ u, (u ∈ insert j U ∧ u ≠ j) ↔ u ∈ U := by
      intro u
      simp only [Finset.mem_insert]
      constructor
      · rintro ⟨h | h, hn⟩
        · exact (hn h).elim
        · exact h
      · intro hu
        exact ⟨Or.inr hu, fun he => hj (he ▸ hu)⟩
    have hWs : ∀ w, (w ∈ insert i W ∧ w ≠ i) ↔ w ∈ W := by
      intro w
      simp only [Finset.mem_insert]
      constructor
      · rintro ⟨h | h, hn⟩
        · exact (hn h).elim
        · exact h
      · intro hw
        exact ⟨Or.inr hw, fun he => hi (he ▸ hw)⟩
    have joining : ∀ t, ¬G.Reachable t j → G.Reachable j i ∨ G.Reachable t i →
        Lawful U W (insert (t, j) F) := by
      intro t hsep hmarkside
      have htj : t ≠ j := fun he => hsep (he ▸ Reachable.refl t)
      have hnewroots := bridge_remove_root G (fun u => u ∈ insert j U)
        hroots t j j (by simp) (Reachable.refl _) hsep
      simp_rw [hUs] at hnewroots
      have hnewmarks : ∀ v, ∃! w, w ∈ W ∧ (G ⊔ edge t j).Reachable v w := by
        rcases hmarkside with hji | hti
        · have hh := bridge_remove_root G (fun w => w ∈ insert i W)
            hmarks t j i (by simp) hji hsep
          simp_rw [hWs] at hh
          exact hh
        · have hh := bridge_remove_root G (fun w => w ∈ insert i W)
            hmarks j t i (by simp) hti (fun h => hsep h.symm)
          simp_rw [hWs] at hh
          simpa only [edge_comm] using hh
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with he | he
        · subst e
          exact htj
        · exact hloop e he
      · intro e he hrev
        rcases Finset.mem_insert.mp he with he | he
        · subst e
          rcases Finset.mem_insert.mp hrev with hrev | hrev
          · exact htj (congrArg Prod.snd hrev)
          · exact hsep (hAdj j t hrev).reachable.symm
        · rcases Finset.mem_insert.mp hrev with hrev | hrev
          · have h₁ := congrArg Prod.fst hrev
            have h₂ := congrArg Prod.snd hrev
            change e.2 = t at h₁
            change e.1 = j at h₂
            apply hsep
            simpa only [h₁, h₂] using (hAdj e.1 e.2 he).reachable.symm
          · exact hanti e he hrev
      · rw [literal_insert_graph]
        exact hacyc.sup_edge_of_not_reachable hsep
      · rw [literal_insert_graph]
        exact hnewroots
      · rw [literal_insert_graph]
        exact hnewmarks
      · intro x y he u hu hur
        have huj : u ≠ j := fun he => hj (he ▸ hu)
        rw [literal_insert_graph] at hur ⊢
        apply bridge_away_orientation E (fun u => u ∈ insert j U) hL hacyc hroots
          (fun x y he u hu hr => haway x y he u hu hr) t j (by simp) hsep
          x y _ u (by simp [hu]) huj hur
        rcases Finset.mem_insert.mp he with he | he
        · exact Or.inr (Prod.mk.inj he)
        · exact Or.inl he
    split_ifs with hd
    · have hji : G.Reachable j i := hdir.mp hd
      have hsep : ¬G.Reachable w₀ j := by
        intro h
        have heq := (hmarks j).unique ⟨by simp [hw₀], h.symm⟩ ⟨by simp, hji⟩
        exact hi (heq ▸ hw₀)
      exact joining w₀ hsep (Or.inl hji)
    · exact joining i (fun h => hd (hdir.mpr h.symm)) (Or.inr (Reachable.refl _))
  
  
  have literal_glue_matching
      (U W : Finset (Fin n)) (F : Finset ((Fin n) × (Fin n))) (i j w₀ : (Fin n))
      (hw₀ : w₀ ∈ W) (hi : i ∉ W) (_hj : j ∉ U)
      (hF : Lawful (insert j U) (insert i W) F)
      (u w : (Fin n)) (hu : u ∈ U) (hw : w ∈ W) :
      (fromRel (fun x y => (x, y) ∈
        (if Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i
          then insert (w₀, j) F else insert (i, j) F))).Reachable u w ↔
      (if Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i
        then (fromRel (fun x y => (x, y) ∈ F)).Reachable u w
        else (fromRel (fun x y => (x, y) ∈ F)).Reachable u w ∨
          ((fromRel (fun x y => (x, y) ∈ F)).Reachable u i ∧
            (fromRel (fun x y => (x, y) ∈ F)).Reachable j w)) := by
    classical
    rcases hF with ⟨hloop, _, _, hroots, hmarks, haway⟩
    let E := fun x y => (x, y) ∈ F
    let G := fromRel E
    have hdir := rooted_directed_reachability E
      (fun x he => hloop (x, x) he rfl) j
      (fun x y he hr => haway x y he j (by simp) hr) i
    have hnuj : ¬G.Reachable u j := by
      intro h
      have he := (hroots j).unique ⟨by simp [hu], h.symm⟩ ⟨by simp, Reachable.refl _⟩
      exact _hj (he ▸ hu)
    split_ifs with hd
    · have hji : G.Reachable j i := hdir.mp hd
      have hnojw : ¬G.Reachable j w := by
        intro h
        have he := (hmarks j).unique ⟨by simp [hw], h⟩ ⟨by simp, hji⟩
        exact hi (he ▸ hw)
      have hn : w₀ ≠ j := by
        intro he
        have hJw : G.Reachable j w₀ := by
          simpa only [he] using (Reachable.refl j : G.Reachable j j)
        have he' : w₀ = i := (hmarks j).unique ⟨by simp [hw₀], hJw⟩
          ⟨by simp, hji⟩
        exact hi (he' ▸ hw₀)
      rw [literal_insert_graph, bridge_reachable_profile G w₀ j hn]
      constructor
      · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
        · exact h
        · exact (hnojw h).elim
        · exact (hnuj h).elim
      · exact Or.inl
    · have hn : i ≠ j := by
        intro he
        exact hd (by simpa [he] using (Relation.ReflTransGen.refl : Relation.ReflTransGen E j j))
      rw [literal_insert_graph, bridge_reachable_profile G i j hn]
      constructor
      · rintro (h | h | ⟨h, _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact (hnuj h).elim
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  
  
  have lawful_add_edge_unchanged
      (U W : Finset (Fin n)) (F : Finset ((Fin n) × (Fin n))) (t j : (Fin n))
      (hF : Lawful U W F) (hH : Lawful U W (insert (t, j) F)) :
      insert (t, j) F = F := by
    classical
    by_cases he : (t, j) ∈ F
    · exact Finset.insert_eq_of_mem he
    rcases hF with ⟨_, _, _, hroots, _, _⟩
    rcases hH with ⟨hloop, hanti, hacyc, hroots', _, _⟩
    let G := fromRel (fun x y => (x, y) ∈ F)
    have htj : t ≠ j := hloop (t, j) (by simp)
    have hnadj : ¬G.Adj t j := by
      rintro ⟨_, he' | he'⟩
      · exact he he'
      · exact hanti (t, j) (by simp) (Finset.mem_insert_of_mem he')
    rw [literal_insert_graph] at hacyc hroots'
    have hsep : ¬G.Reachable t j := by
      intro h
      exact ((isAcyclic_sup_fromEdgeSet_iff.mp hacyc).2 h).elim htj hnadj
    obtain ⟨r, hr, _⟩ := hroots t
    obtain ⟨s, hs, _⟩ := hroots j
    have hadj : (G ⊔ edge t j).Adj t j :=
      Or.inr ((edge_adj t j t j).mpr ⟨Or.inl ⟨rfl, rfl⟩, htj⟩)
    have heq := (hroots' t).unique
      ⟨hr.1, hr.2.mono le_sup_left⟩
      ⟨hs.1, hadj.reachable.trans (hs.2.mono le_sup_left)⟩
    exact (hsep (hr.2.trans (heq ▸ hs.2).symm)).elim
  
  
  have lawful_cut_root_outside
      (U W : Finset (Fin n)) (F : Finset ((Fin n) × (Fin n))) (i j : (Fin n))
      (hF : Lawful U W F) (he : (i, j) ∈ F) :
      let C := fromRel (fun x y => (x, y) ∈ F.erase (i, j))
      C.IsAcyclic ∧ ¬C.Reachable i j ∧ ∀ u ∈ U, ¬C.Reachable u j := by
    classical
    dsimp only
    let G := fromRel (fun x y => (x, y) ∈ F)
    let C := fromRel (fun x y => (x, y) ∈ F.erase (i, j))
    rcases hF with ⟨hloop, hanti, hacyc, _, _, haway⟩
    have hg : G = C ⊔ edge i j := by
      dsimp [G, C]
      rw [← literal_insert_graph, Finset.insert_erase he]
    have hc : (C ⊔ edge i j).IsAcyclic := by rw [← hg]; exact hacyc
    have hne : i ≠ j := hloop (i, j) he
    have hnadj : ¬C.Adj i j := by
      rintro ⟨_, h | h⟩
      · simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at h
      · exact hanti (i, j) he (Finset.mem_erase.mp h).2
    have hsep : ¬C.Reachable i j := by
      intro h
      exact ((isAcyclic_sup_fromEdgeSet_iff.mp hc).2 h).elim hne hnadj
    have ha : C.IsAcyclic := hc.anti le_sup_left
    refine ⟨ha, hsep, ?_⟩
    intro u hu hreach
    have hle : C ≤ G := by rw [hg]; exact le_sup_left
    have hji : G.Adj j i := ⟨hne.symm, Or.inr he⟩
    have hlt := haway i j he u hu ((hreach.mono hle).trans hji.reachable)
    have hdj := bridge_old_distance C ha i j hsep hreach
    rw [← hg] at hdj
    have hdi := bridge_cross_distance C ha j i (fun h => hsep h.symm)
      hreach (Reachable.refl i)
    rw [edge_comm, ← hg] at hdi
    simp only [dist_self, add_zero] at hdi
    change G.dist u i < G.dist u j at hlt
    rw [hdi, hdj] at hlt
    omega
  
  
  have literal_reattachment_matching
      (U W : Finset (Fin n)) (F : Finset ((Fin n) × (Fin n))) (i j w₀ : (Fin n))
      (hw₀ : w₀ ∈ W) (hF : Lawful U W F)
      (hF' : Lawful U W (insert (w₀, j) (F.erase (i, j))))
      (u w : (Fin n)) (hu : u ∈ U) (hw : w ∈ W) :
      (fromRel (fun x y => (x, y) ∈ F)).Reachable u w ↔
        (fromRel (fun x y => (x, y) ∈ insert (w₀, j) (F.erase (i, j)))).Reachable u w := by
    classical
    by_cases hs : insert (w₀, j) (F.erase (i, j)) = F
    · rw [hs]
    have he : (i, j) ∈ F := by
      by_contra he
      have her : F.erase (i, j) = F := Finset.erase_eq_of_notMem he
      have ha := lawful_add_edge_unchanged U W F w₀ j hF (by simpa only [her] using hF')
      exact hs (by simpa only [her] using ha)
    let C := fromRel (fun x y => (x, y) ∈ F.erase (i, j))
    let G := fromRel (fun x y => (x, y) ∈ F)
    let H := fromRel (fun x y => (x, y) ∈ insert (w₀, j) (F.erase (i, j)))
    have hg : G = C ⊔ edge i j := by
      dsimp [G, C]
      rw [← literal_insert_graph, Finset.insert_erase he]
    have hh : H = C ⊔ edge w₀ j := literal_insert_graph (F.erase (i, j)) w₀ j
    obtain ⟨hC, hsep, hnoroot⟩ := lawful_cut_root_outside U W F i j hF he
    have hnew : (w₀, j) ∉ F.erase (i, j) := by
      intro hnew
      have hroot := hF'.2.2.2.1 j
      rw [Finset.insert_eq_of_mem hnew] at hroot
      obtain ⟨r, hr, _⟩ := hroot
      exact hnoroot r hr.1 hr.2.symm
    have hnewmem : (w₀, j) ∈ insert (w₀, j) (F.erase (i, j)) := by simp
    have hn : w₀ ≠ j := hF'.1 (w₀, j) hnewmem
    have hnAdj : ¬C.Adj w₀ j := by
      rintro ⟨_, h | h⟩
      · exact hnew h
      · exact hF'.2.1 (w₀, j) hnewmem (Finset.mem_insert_of_mem h)
    have hnewsep : ¬C.Reachable w₀ j := by
      have ha := hF'.2.2.1
      rw [literal_insert_graph] at ha
      intro h
      exact ((isAcyclic_sup_fromEdgeSet_iff.mp ha).2 h).elim hn hnAdj
    have hle : C ≤ H := by rw [hh]; exact le_sup_left
    have hAdj : H.Adj w₀ j := ⟨hn, Or.inl hnewmem⟩
    have hnomark : ∀ w ∈ W, ¬C.Reachable j w := by
      intro w hw hreach
      have heq : w = w₀ := (hF'.2.2.2.2.1 j).unique
        ⟨hw, hreach.mono hle⟩ ⟨hw₀, hAdj.reachable.symm⟩
      exact hnewsep (heq ▸ hreach.symm)
    have preservation : ∀ u ∈ U, ∀ w ∈ W, G.Reachable u w → H.Reachable u w := by
      intro u hu w hw hreach
      rw [hg] at hreach
      have hij : i ≠ j := hF.1 (i, j) he
      rcases (bridge_reachable_profile C i j hij u w).mp hreach with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact h.mono hle
      · exact (hnomark w hw h).elim
      · exact (hnoroot u hu h).elim
    constructor
    · exact preservation u hu w hw
    · intro hreach
      obtain ⟨v, hv, _⟩ := hF.2.2.2.2.1 u
      have hp := preservation u hu v hv.1 hv.2
      have heq : w = v := (hF'.2.2.2.2.1 u).unique ⟨hw, hreach⟩ ⟨hv.1, hp⟩
      exact heq ▸ hv.2
  
  have ascending_deletion_coordinates
      (U : Finset (Fin n)) (j : (Fin n)) (hj : j ∉ U) (k : ℕ) (hU : U.card = k) :
      let hAug : (insert j U).card = k + 1 := by simp [hj, hU]
      let a := (insert j U).orderIsoOfFin hAug |>.symm ⟨j, by simp⟩
      (insert j U).orderEmbOfFin hAug a = j ∧
      (∀ r : Fin k, (insert j U).orderEmbOfFin hAug (a.succAbove r) =
        U.orderEmbOfFin hU r) ∧ a.val = (U.filter (· < j)).card := by
    classical
    dsimp only
    let hAug : (insert j U).card = k + 1 := by simp [hj, hU]
    let a := (insert j U).orderIsoOfFin hAug |>.symm ⟨j, by simp⟩
    let e := (insert j U).orderEmbOfFin hAug
    have ha : e a = j := by
      change (((insert j U).orderIsoOfFin hAug) a).val = j
      simp only [a, OrderIso.apply_symm_apply]
    have hmem : ∀ r : Fin k, e (a.succAbove r) ∈ U := by
      intro r
      have hm := (insert j U).orderEmbOfFin_mem hAug (a.succAbove r)
      rcases Finset.mem_insert.mp hm with hh | hh
      · have hn := e.injective (hh.trans ha.symm)
        exact (Fin.succAbove_ne a r hn).elim
      · exact hh
    have he : (fun r : Fin k => e (a.succAbove r)) = U.orderEmbOfFin hU :=
      Finset.orderEmbOfFin_unique hU hmem (e.strictMono.comp (Fin.strictMono_succAbove a))
    have hfilter : (insert j U).filter (· < j) =
        (Finset.univ.filter (fun r : Fin (k + 1) => r < a)).image e := by
      conv_lhs => rw [← Finset.image_orderEmbOfFin_univ (insert j U) hAug]
      rw [Finset.filter_image]
      congr 1
      apply Finset.filter_congr
      intro r _
      change e r < j ↔ r < a
      rw [← ha]
      exact e.lt_iff_lt
    have hcard : ((insert j U).filter (· < j)).card = a.val := by
      rw [hfilter, Finset.card_image_of_injective _ e.injective,
        Finset.filter_gt_eq_Iio, Fin.card_Iio]
    refine ⟨ha, fun r => congrFun he r, ?_⟩
    simpa only [Finset.filter_insert, lt_self_iff_false, ite_false] using hcard.symm
  
  have actual_glued_matching_sign {k : ℕ} (U W : Finset (Fin n))
      (hU : U.card = k) (hW : W.card = k) (F : Finset (Fin n × Fin n))
      (i j w₀ : Fin n) (hw₀ : w₀ ∈ W) (hi : i ∉ W) (hj : j ∉ U)
      (hF : Lawful (insert j U) (insert i W) F)
      (sigmaPlus : Equiv.Perm (Fin (k + 1))) (σ : Equiv.Perm (Fin k))
      (hSigmaPlus : ∀ r, (fromRel (fun x y => (x, y) ∈ F)).Reachable
        ((insert j U).orderEmbOfFin (by simp [hj, hU]) r)
        ((insert i W).orderEmbOfFin (by simp [hi, hW]) (sigmaPlus r)))
      (hσ : ∀ r, (fromRel (fun x y => (x, y) ∈
        (if Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i
          then insert (w₀, j) F else insert (i, j) F))).Reachable
        (U.orderEmbOfFin hU r) (W.orderEmbOfFin hW (σ r))) :
      (Equiv.Perm.sign sigmaPlus : ℤ) =
        (-1 : ℤ) ^ ((U.filter (· < j)).card + (W.filter (· < i)).card) *
        (if Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i then 1 else -1) *
        (Equiv.Perm.sign σ : ℤ) := by
    classical
    let G := fromRel (fun x y => (x, y) ∈ F)
    let D := Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i
    let H := fromRel (fun x y => (x, y) ∈ (if D then insert (w₀, j) F else insert (i, j) F))
    let hUPlus : (insert j U).card = k + 1 := by simp [hj, hU]
    let hWPlus : (insert i W).card = k + 1 := by simp [hi, hW]
    let a := (insert j U).orderIsoOfFin hUPlus |>.symm ⟨j, by simp⟩
    let b := (insert i W).orderIsoOfFin hWPlus |>.symm ⟨i, by simp⟩
    let eU := (insert j U).orderEmbOfFin hUPlus
    let eW := (insert i W).orderEmbOfFin hWPlus
    change ∀ r, G.Reachable (eU r) (eW (sigmaPlus r)) at hSigmaPlus
    have cU := ascending_deletion_coordinates U j hj k hU
    have cW := ascending_deletion_coordinates W i hi k hW
    change eU a = j ∧ (∀ r, eU (a.succAbove r) = U.orderEmbOfFin hU r) ∧
      a.val = (U.filter (· < j)).card at cU
    change eW b = i ∧ (∀ r, eW (b.succAbove r) = W.orderEmbOfFin hW r) ∧
      b.val = (W.filter (· < i)).card at cW
    let Q := b.cycleRange * sigmaPlus * a.cycleRange.symm
    let p := (Equiv.Perm.decomposeFin Q).1
    let ρ := (Equiv.Perm.decomposeFin Q).2
    have hrep : Equiv.Perm.decomposeFin.symm (p, ρ) = Q :=
      Equiv.Perm.decomposeFin.symm_apply_apply Q
    have hp : p = Q 0 := by
      rw [← hrep]
      exact (Equiv.Perm.decomposeFin_symm_apply_zero p ρ).symm
    have hQzero : Q 0 = b.cycleRange (sigmaPlus a) := by simp [Q, Equiv.Perm.mul_apply]
    have hQsucc (r : Fin k) : Q r.succ = b.cycleRange (sigmaPlus (a.succAbove r)) := by
      simp [Q, Equiv.Perm.mul_apply]
    have hsucc (r : Fin k) : Q r.succ = Equiv.swap 0 p (ρ r).succ := by
      rw [← hrep]
      exact Equiv.Perm.decomposeFin_symm_apply_succ ρ p r
    have hdir := rooted_directed_reachability (fun x y => (x, y) ∈ F)
      (fun x he => hF.1 (x, x) he rfl) j
      (fun x y he hr => hF.2.2.2.2.2 x y he j (by simp) hr) i
    have hfixed : sigmaPlus a = b ↔ D := by
      constructor
      · intro h
        apply hdir.mpr
        simpa only [h, cU.1, cW.1] using hSigmaPlus a
      · intro hd
        have hmatch := hSigmaPlus a
        rw [cU.1] at hmatch
        have hi' := hdir.mp hd
        have heq := (hF.2.2.2.2.1 j).unique
          ⟨(insert i W).orderEmbOfFin_mem hWPlus (sigmaPlus a), hmatch⟩
          ⟨by simp, hi'⟩
        exact eW.injective (heq.trans cW.1.symm)
    have hpzero : p = 0 ↔ D := by
      rw [hp, hQzero]
      constructor
      · intro h
        exact hfixed.mp (b.cycleRange.injective (h.trans (by simp)))
      · intro h
        rw [hfixed.mpr h]
        simp
    have hmigrate : ∀ r, H.Reachable (U.orderEmbOfFin hU r)
        (W.orderEmbOfFin hW (ρ r)) := by
      intro r
      have hbridge := literal_glue_matching U W F i j w₀ hw₀ hi hj hF
        (U.orderEmbOfFin hU r) (W.orderEmbOfFin hW (ρ r))
        (U.orderEmbOfFin_mem hU r) (W.orderEmbOfFin_mem hW (ρ r))
      apply hbridge.mpr
      change if D then G.Reachable (U.orderEmbOfFin hU r) (W.orderEmbOfFin hW (ρ r))
        else G.Reachable (U.orderEmbOfFin hU r) (W.orderEmbOfFin hW (ρ r)) ∨
          (G.Reachable (U.orderEmbOfFin hU r) i ∧ G.Reachable j (W.orderEmbOfFin hW (ρ r)))
      by_cases hd : D
      · have hper : sigmaPlus (a.succAbove r) = b.succAbove (ρ r) := by
          apply b.cycleRange.injective
          rw [← hQsucc, hsucc, hpzero.mpr hd]
          simp
        have hr := hSigmaPlus (a.succAbove r)
        simpa only [hper, cU.2.1 r, cW.2.1 (ρ r), if_pos hd] using hr
      · by_cases hskip : sigmaPlus (a.succAbove r) = b
        · have hz : Q r.succ = 0 := by rw [hQsucc, hskip]; simp
          have hrho : (ρ r).succ = p := by
            apply (Equiv.swap 0 p).injective
            rw [← hsucc, hz, Equiv.swap_apply_right]
          have hper : sigmaPlus a = b.succAbove (ρ r) := by
            apply b.cycleRange.injective
            rw [← hQzero, ← hp, Fin.cycleRange_succAbove, hrho]
          have hr := hSigmaPlus (a.succAbove r)
          have ha := hSigmaPlus a
          have hri : G.Reachable (U.orderEmbOfFin hU r) i := by
            simpa only [hskip, cU.2.1 r, cW.1] using hr
          have hjw : G.Reachable j (W.orderEmbOfFin hW (ρ r)) := by
            simpa only [hper, cU.1, cW.2.1 (ρ r)] using ha
          simpa only [if_neg hd] using (Or.inr ⟨hri, hjw⟩ :
            G.Reachable (U.orderEmbOfFin hU r) (W.orderEmbOfFin hW (ρ r)) ∨
              (G.Reachable (U.orderEmbOfFin hU r) i ∧ G.Reachable j (W.orderEmbOfFin hW (ρ r))))
        · have hz : Q r.succ ≠ 0 := by
            intro h
            exact hskip (b.cycleRange.injective ((hQsucc r).symm.trans (h.trans (by simp))))
          have hnp : Q r.succ ≠ p := by
            intro h
            exact Fin.succ_ne_zero r (Q.injective (h.trans hp))
          have hqr : Q r.succ = (ρ r).succ := by
            calc
              Q r.succ = Equiv.swap 0 p (Q r.succ) :=
                (Equiv.swap_apply_of_ne_of_ne hz hnp).symm
              _ = (ρ r).succ := by rw [hsucc]; simp
          have hper : sigmaPlus (a.succAbove r) = b.succAbove (ρ r) := by
            apply b.cycleRange.injective
            rw [← hQsucc, hqr, Fin.cycleRange_succAbove]
          have hr := hSigmaPlus (a.succAbove r)
          have hrw : G.Reachable (U.orderEmbOfFin hU r) (W.orderEmbOfFin hW (ρ r)) := by
            simpa only [hper, cU.2.1 r, cW.2.1 (ρ r)] using hr
          simpa only [if_neg hd] using (Or.inl hrw :
            G.Reachable (U.orderEmbOfFin hU r) (W.orderEmbOfFin hW (ρ r)) ∨
              (G.Reachable (U.orderEmbOfFin hU r) i ∧ G.Reachable j (W.orderEmbOfFin hW (ρ r))))
    have hρ : ρ = σ := by
      have hlegal := literal_glue_lawful U W F i j w₀ hw₀ hi hj hF
      apply Equiv.ext
      intro r
      apply (W.orderEmbOfFin hW).injective
      exact (hlegal.2.2.2.2.1 (U.orderEmbOfFin hU r)).unique
        ⟨W.orderEmbOfFin_mem hW (ρ r), hmigrate r⟩
        ⟨W.orderEmbOfFin_mem hW (σ r), hσ r⟩
    have hsign := Equiv.Perm.decomposeFin.symm_sign p ρ
    rw [hrep, hρ] at hsign
    simp only [hpzero] at hsign
    have hsignQ : Equiv.Perm.sign Q =
        (-1 : ℤˣ) ^ (a.val + b.val) * Equiv.Perm.sign sigmaPlus := by
      simp only [Q, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, pow_add]
      ac_rfl
    rw [hsignQ] at hsign
    have hsq : (-1 : ℤˣ) ^ (a.val + b.val) * (-1 : ℤˣ) ^ (a.val + b.val) = 1 := by
      rw [← mul_pow]
      simp
    have hunit : Equiv.Perm.sign sigmaPlus = (-1 : ℤˣ) ^ (a.val + b.val) *
        (if D then 1 else -1) * Equiv.Perm.sign σ := by
      calc
        Equiv.Perm.sign sigmaPlus = (-1 : ℤˣ) ^ (a.val + b.val) *
            ((-1 : ℤˣ) ^ (a.val + b.val) * Equiv.Perm.sign sigmaPlus) := by
          rw [← mul_assoc, hsq, one_mul]
        _ = (-1 : ℤˣ) ^ (a.val + b.val) * ((if D then 1 else -1) * Equiv.Perm.sign σ) :=
          congrArg (fun z => (-1 : ℤˣ) ^ (a.val + b.val) * z) hsign
        _ = _ := by rw [mul_assoc]
    have hv := congrArg (fun z : ℤˣ => (z : ℤ)) hunit
    change (Equiv.Perm.sign sigmaPlus : ℤ) =
      (-1 : ℤ) ^ ((U.filter (· < j)).card + (W.filter (· < i)).card) *
      (if D then 1 else -1) * (Equiv.Perm.sign σ : ℤ)
    by_cases hd : D
    · simpa [hd, cU.2.2, cW.2.2] using hv
    · simpa [hd, cU.2.2, cW.2.2] using hv

  have existing (k : ℕ) (U W : Finset (Fin n)) (hU : U.card = k) (hW : W.card = k)
      (hk : 1 ≤ k) : ∃ m : (F : Finset (Fin n × Fin n)) → Lawful U W F → Equiv.Perm (Fin k),
      ∀ F hF a, (fromRel (fun x y => (x, y) ∈ F)).Reachable
        (U.orderEmbOfFin hU a) (W.orderEmbOfFin hW (m F hF a)) := by
    obtain ⟨m, hm, _⟩ :=
      D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.directed_all_minors_matrix_tree
        (R := ℤ) (0 : Matrix (Fin n) (Fin n) ℤ) U W hU hW hk (by simp)
    refine ⟨fun F hF => m ⟨F, ⟨hF.1, hF.2.2⟩⟩, ?_⟩
    intro F hF a
    exact hm ⟨F, ⟨hF.1, hF.2.2⟩⟩ a
  let μ : (k : ℕ) → (U W : Finset (Fin n)) → U.card = k → W.card = k →
      (F : Finset (Fin n × Fin n)) → Lawful U W F → Equiv.Perm (Fin k) :=
    fun k U W hU hW F hF => if hk : 1 ≤ k then (existing k U W hU hW hk).choose F hF
      else Equiv.refl _
  have spec (k : ℕ) (U W : Finset (Fin n)) (hU : U.card = k) (hW : W.card = k)
      (F : Finset (Fin n × Fin n)) (hF : Lawful U W F) (a : Fin k) :
      (fromRel (fun x y => (x, y) ∈ F)).Reachable (U.orderEmbOfFin hU a)
        (W.orderEmbOfFin hW (μ k U W hU hW F hF a)) := by
    dsimp only [μ]
    split_ifs with hk
    · exact (existing k U W hU hW hk).choose_spec F hF a
    · have ha := a.isLt
      omega
  refine ⟨μ, spec, ?_, ?_, ?_⟩
  · have hEg : fromRel (fun x y : Fin n => (x, y) ∈ (∅ : Finset (Fin n × Fin n))) = ⊥ := by
      ext x y
      simp
    have hempty : Lawful Finset.univ Finset.univ (∅ : Finset (Fin n × Fin n)) := by
      refine ⟨by simp, by simp, ?_, ?_, ?_, by simp⟩
      · rw [hEg]
        exact isAcyclic_bot
      · intro v
        rw [hEg]
        simp [reachable_bot]
      · intro v
        rw [hEg]
        simp [reachable_bot]
    refine ⟨hempty, ?_⟩
    have hperm : μ n Finset.univ Finset.univ (by simp) (by simp) ∅ hempty = Equiv.refl _ := by
      apply Equiv.ext
      intro a
      apply (Finset.univ.orderEmbOfFin (by simp : (Finset.univ : Finset (Fin n)).card = n)).injective
      have hr := spec n Finset.univ Finset.univ (by simp) (by simp) ∅ hempty a
      rw [hEg, reachable_bot] at hr
      exact hr.symm
    change (-1 : ℤ) ^ (n + n + (∑ u : Fin n, u.val) + (∑ u : Fin n, u.val)) *
      (Equiv.Perm.sign (μ n Finset.univ Finset.univ (by simp) (by simp) ∅ hempty) : ℤ) = 1
    rw [hperm]
    simp only [Equiv.Perm.sign_refl, Units.val_one, mul_one]
    have he : n + n + (∑ u : Fin n, u.val) + (∑ u : Fin n, u.val) =
        2 * (n + ∑ u : Fin n, u.val) := by omega
    rw [he, pow_mul]
    norm_num
  · intro k _hk U W hU hW w₀ i j hw₀ hi hj F hF
    let D := Relation.ReflTransGen (fun x y => (x, y) ∈ F) j i
    let H := if D then insert (w₀, j) F else insert (i, j) F
    have hH : Lawful U W H := literal_glue_lawful U W F i j w₀ hw₀ hi hj hF
    refine ⟨hH, ?_⟩
    let hUPlus : (insert j U).card = k + 1 := by simp [hj, hU]
    let hWPlus : (insert i W).card = k + 1 := by simp [hi, hW]
    let sigmaPlus := μ (k + 1) (insert j U) (insert i W) hUPlus hWPlus F hF
    let sigma := μ k U W hU hW H hH
    have hs := actual_glued_matching_sign U W hU hW F i j w₀ hw₀ hi hj hF
      sigmaPlus sigma (spec (k + 1) (insert j U) (insert i W) hUPlus hWPlus F hF)
      (spec k U W hU hW H hH)
    let a := (U.filter (· < j)).card
    let b := (W.filter (· < i)).card
    let sU := ∑ u ∈ U, u.val
    let sW := ∑ w ∈ W, w.val
    change (Equiv.Perm.sign sigmaPlus : ℤ) =
      (-1 : ℤ) ^ (a + b) * (if D then 1 else -1) * (Equiv.Perm.sign sigma : ℤ) at hs
    change (-1 : ℤ) ^ (i.val + b + j.val + a) *
      ((-1 : ℤ) ^ (n + (k + 1) + (∑ u ∈ insert j U, u.val) + (∑ w ∈ insert i W, w.val)) *
        (Equiv.Perm.sign sigmaPlus : ℤ)) =
      (if D then -1 else 1) * ((-1 : ℤ) ^ (n + k + sU + sW) * (Equiv.Perm.sign sigma : ℤ))
    rw [Finset.sum_insert hj, Finset.sum_insert hi, hs]
    change (-1 : ℤ) ^ (i.val + b + j.val + a) *
      ((-1 : ℤ) ^ (n + (k + 1) + (j.val + sU) + (i.val + sW)) *
        ((-1 : ℤ) ^ (a + b) * (if D then 1 else -1) * (Equiv.Perm.sign sigma : ℤ))) = _
    have hpows : (-1 : ℤ) ^ (i.val + b + j.val + a) *
        (-1 : ℤ) ^ (n + (k + 1) + (j.val + sU) + (i.val + sW)) * (-1 : ℤ) ^ (a + b) =
        -((-1 : ℤ) ^ (n + k + sU + sW)) := by
      rw [← pow_add, ← pow_add]
      have he : i.val + b + j.val + a + (n + (k + 1) + (j.val + sU) + (i.val + sW)) + (a + b) =
          n + k + sU + sW + 1 + 2 * (i.val + j.val + a + b) := by omega
      rw [he, pow_add, pow_add, pow_mul]
      norm_num
    calc
      _ = ((-1 : ℤ) ^ (i.val + b + j.val + a) *
          (-1 : ℤ) ^ (n + (k + 1) + (j.val + sU) + (i.val + sW)) * (-1 : ℤ) ^ (a + b)) *
          (if D then 1 else -1) * (Equiv.Perm.sign sigma : ℤ) := by ring
      _ = _ := by rw [hpows]; split_ifs <;> ring
  · intro k _hk U W hU hW i j w₀ hw₀ F hF hF'
    have heq : μ k U W hU hW F hF = μ k U W hU hW (insert (w₀, j) (F.erase (i, j))) hF' := by
      apply Equiv.ext
      intro a
      apply (W.orderEmbOfFin hW).injective
      have hm := spec k U W hU hW F hF a
      have hp := (literal_reattachment_matching U W F i j w₀ hw₀ hF hF'
        (U.orderEmbOfFin hU a) (W.orderEmbOfFin hW (μ k U W hU hW F hF a))
        (U.orderEmbOfFin_mem hU a)
        (W.orderEmbOfFin_mem hW (μ k U W hU hW F hF a))).mp hm
      exact (hF'.2.2.2.2.1 (U.orderEmbOfFin hU a)).unique
        ⟨W.orderEmbOfFin_mem hW (μ k U W hU hW F hF a), hp⟩
        ⟨W.orderEmbOfFin_mem hW (μ k U W hU hW (insert (w₀, j) (F.erase (i, j))) hF' a),
          spec k U W hU hW (insert (w₀, j) (F.erase (i, j))) hF' a⟩
    change (-1 : ℤ) ^ (n + k + (∑ u ∈ U, u.val) + (∑ w ∈ W, w.val)) *
      (Equiv.Perm.sign (μ k U W hU hW F hF) : ℤ) = _
    rw [heq]

end D5.S3.Combinatorics.Graph.DirectedForestGluingSigns
