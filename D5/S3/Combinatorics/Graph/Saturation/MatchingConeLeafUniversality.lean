/- GID: D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality
   mirror-E: none(waiver:structural-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Copy, mathlib/module/Mathlib.Combinatorics.SimpleGraph.DeleteEdges, mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: In a sparse maximal matching-cone-free finite graph, every leaf has a universal neighbor. -/
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Order.Minimal
import Mathlib.Tactic

namespace D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality

open SimpleGraph Finset

/-- The cone over three disjoint edges and one isolated vertex. The left
unit is the center; the right-left unit is the pendant. -/
def H : SimpleGraph (Unit ⊕ (Unit ⊕ (Fin 3 × Bool))) where
  Adj a b := match a, b with
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr (.inr (i, s)), .inr (.inr (j, t)) => i = j ∧ s ≠ t
    | _, _ => False
  symm := ⟨by
    intro a b h
    rcases a with a | (a | ⟨i, s⟩) <;>
      rcases b with b | (b | ⟨j, t⟩) <;> simp_all [eq_comm]⟩
  loopless := ⟨by
    intro a
    rcases a with a | (a | ⟨i, s⟩) <;> simp⟩

set_option maxHeartbeats 1200000 in
-- The role and incidence arguments form one dependent proof term.
/-- No order cutoff or connectivity hypothesis is needed. Copies preserve
required adjacency and are permitted to have extra edges. -/
theorem leaf_neighbor_isUniversal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : Maximal H.Free G)
    (hedges : G.edgeFinset.card ≤ Fintype.card V + 5)
    {u v : V} (hdegree : G.degree u = 1) (huv : G.Adj u v) :
    G.IsUniversal v := by
  classical
  have hfree := hmax.prop
  have hleaf : ∀ y, G.Adj u y → y = v := by
    obtain ⟨w, hw, he⟩ := degree_eq_one_iff_existsUnique_adj.mp hdegree
    intro y hy
    exact (he y hy).trans (he v huv).symm
  let B := univ.filter (fun x : V => x ≠ v ∧ ¬G.Adj v x)
  let D := G.deleteIncidenceSet v
  have hstructure : ∀ x ∈ B, ∃ f : H.Copy (G ⊔ edge u x),
      f (.inl ()) = x ∧ f (.inr (.inl ())) = u ∧
      (∀ a b, a ≠ .inr (.inl ()) → b ≠ .inr (.inl ()) →
        H.Adj a b → G.Adj (f a) (f b)) ∧
      G.neighborFinset x = univ.image (fun z : Fin 3 × Bool => f (.inr (.inr z))) := by
    intro x hx
    have hxv : x ≠ v := (mem_filter.mp hx).2.1
    have hvx : ¬G.Adj v x := (mem_filter.mp hx).2.2
    have hxu : x ≠ u := by
      intro he
      exact hvx (he.symm ▸ huv.symm)
    have hux : ¬G.Adj u x := fun h => hxv (hleaf x h)
    let J := G ⊔ edge u x
    have hJ : ¬H.Free J := hmax.not_prop_of_gt (G.lt_sup_edge u x hxu.symm hux)
    obtain ⟨f⟩ := not_free.mp hJ
    have hJu : ∀ y, J.Adj u y → y = v ∨ y = x := by
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (hleaf y hy)
      · simp only [edge_adj] at hy
        rcases hy.1 with h | h
        · exact Or.inr h.2
        · exact False.elim (hxu h.1.symm)
    have htriangle : ∀ a b, J.Adj u a → J.Adj u b → J.Adj a b → False := by
      intro a b ha hb hab
      rcases hJu a ha with rfl | rfl <;>
        rcases hJu b hb with rfl | rfl
      · exact J.ne_of_adj hab rfl
      · rcases hab with h | h
        · exact hvx h
        · simp only [edge_adj] at h
          rcases h.1 with h | h
          · exact huv.ne h.1.symm
          · exact hxv h.1.symm
      · exact hvx (by
          rcases hab.symm with h | h
          · exact h
          · simp only [edge_adj] at h
            rcases h.1 with h | h
            · exact False.elim (huv.ne h.1.symm)
            · exact False.elim (hxv h.1.symm))
      · exact J.ne_of_adj hab rfl
    have hrole : ∀ a, f a = u → a = .inr (.inl ()) := by
      intro a ha
      rcases a with a | (a | ⟨i, s⟩)
      · cases a
        have h1 := f.toHom.map_rel (show H.Adj (.inl ()) (.inr (.inr (0, false))) by trivial)
        have h2 := f.toHom.map_rel (show H.Adj (.inl ()) (.inr (.inr (0, true))) by trivial)
        have h3 := f.toHom.map_rel (show H.Adj (.inr (.inr (0, false))) (.inr (.inr (0, true))) by simp [H])
        simp only [Copy.toHom_apply] at h1 h2 h3
        rw [ha] at h1 h2
        exact False.elim (htriangle _ _ h1 h2 h3)
      · cases a
        rfl
      · have h1 := f.toHom.map_rel (show H.Adj (.inr (.inr (i, s))) (.inl ()) by trivial)
        have h2 := f.toHom.map_rel (show H.Adj (.inr (.inr (i, s))) (.inr (.inr (i, !s))) by cases s <;> simp [H])
        have h3 := f.toHom.map_rel (show H.Adj (.inl ()) (.inr (.inr (i, !s))) by trivial)
        simp only [Copy.toHom_apply] at h1 h2 h3
        rw [ha] at h1 h2
        exact False.elim (htriangle _ _ h1 h2 h3)
    have hnew : ∃ a b, H.Adj a b ∧ ¬G.Adj (f a) (f b) := by
      by_contra hn
      push Not at hn
      exact hfree ⟨{ toHom := ⟨f, fun hab => hn _ _ hab⟩, injective' := f.injective }⟩
    obtain ⟨a, b, hab, hn⟩ := hnew
    have hadded : (edge u x).Adj (f a) (f b) := (f.toHom.map_rel hab).resolve_left hn
    have hp : f (.inr (.inl ())) = u := by
      rcases (edge_adj _ _ _ _).mp hadded with ⟨h | h, _⟩
      · exact (hrole a h.1) ▸ h.1
      · exact (hrole b h.2) ▸ h.2
    have hc : f (.inl ()) = x := by
      rcases (edge_adj _ _ _ _).mp hadded with ⟨h | h, _⟩
      · have ha := hrole a h.1
        subst a
        have hb : b = .inl () := by
          rcases b with ⟨⟩ | (⟨⟩ | b)
          · rfl
          · exact hab.elim
          · exact hab.elim
        exact hb ▸ h.2
      · have hb := hrole b h.2
        subst b
        have ha : a = .inl () := by
          rcases a with ⟨⟩ | (⟨⟩ | a)
          · rfl
          · exact hab.elim
          · exact hab.elim
        exact ha ▸ h.1
    have hold : ∀ a b, a ≠ .inr (.inl ()) → b ≠ .inr (.inl ()) →
        H.Adj a b → G.Adj (f a) (f b) := by
      intro a b ha hb hab
      rcases f.toHom.map_rel hab with h | h
      · exact h
      · rcases (edge_adj _ _ _ _).mp h with ⟨h | h, _⟩
        · exact False.elim (ha (hrole a h.1))
        · exact False.elim (hb (hrole b h.2))
    refine ⟨f, hc, hp, hold, ?_⟩
    apply Finset.ext
    intro y
    constructor
    · intro hy
      have hxy := (mem_neighborFinset G x y).mp hy
      by_contra hn
      have hyroles : ∀ z : Fin 3 × Bool, y ≠ f (.inr (.inr z)) := by
        intro z he
        exact hn (mem_image.mpr ⟨z, mem_univ _, he.symm⟩)
      let g : Unit ⊕ (Unit ⊕ (Fin 3 × Bool)) → V := fun a =>
        match a with
        | .inr (.inl _) => y
        | _ => f a
      have hginj : Function.Injective g := by
        intro a b he
        rcases a with ⟨⟩ | (⟨⟩ | a) <;> rcases b with ⟨⟩ | (⟨⟩ | b)
        all_goals try rfl
        all_goals simp only [g] at he
        all_goals try { exact f.injective he }
        all_goals try { exact False.elim (hxy.ne (hc ▸ he)) }
        all_goals try { exact False.elim (hxy.ne (hc ▸ he.symm)) }
        all_goals try { exact False.elim (hyroles _ he) }
        all_goals try { exact False.elim (hyroles _ he.symm) }
      have hgadj : ∀ a b, H.Adj a b → G.Adj (g a) (g b) := by
        intro a b hab
        rcases a with ⟨⟩ | (⟨⟩ | a) <;> rcases b with ⟨⟩ | (⟨⟩ | b)
        all_goals simp only [H] at hab
        all_goals try { simpa [g, hc] using hxy }
        all_goals try { simpa [g, hc] using hxy.symm }
        all_goals exact hold _ _ (by simp) (by simp) hab
      exact hfree ⟨{ toHom := ⟨g, fun hab => hgadj _ _ hab⟩, injective' := hginj }⟩
    · intro hy
      obtain ⟨z, _, rfl⟩ := mem_image.mp hy
      apply (mem_neighborFinset G x _).mpr
      simpa only [hc] using (hold (.inl ()) (.inr (.inr z))
        (by simp) (by simp) (by trivial))
  have hDdegree : ∀ x ∈ B, D.degree x = 6 := by
    intro x hx
    obtain ⟨f, hc, hp, hold, hn⟩ := hstructure x hx
    have hGdegree : G.degree x = 6 := by
      rw [← card_neighborFinset_eq_degree, hn,
        card_image_of_injective _ (by
          intro a b he
          exact Sum.inr.inj (Sum.inr.inj (f.injective he)))]
      simp
    have hneigh : D.neighborFinset x = G.neighborFinset x := by
      ext y
      simp only [mem_neighborFinset]
      change (G.deleteIncidenceSet v).Adj x y ↔ G.Adj x y
      rw [deleteIncidenceSet_adj]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, (mem_filter.mp hx).2.1, ?_⟩
        intro he
        exact (mem_filter.mp hx).2.2 (he ▸ h.symm)
    simpa only [degree, hneigh] using hGdegree
  have hpartition : G.degree v + B.card + 1 = Fintype.card V := by
    have hcover : insert v (G.neighborFinset v) ∪ B = univ := by
      ext y
      simp only [mem_union, mem_insert, mem_neighborFinset, B, mem_filter, mem_univ,
        true_and, iff_true]
      by_cases hy : y = v
      · exact Or.inl (Or.inl hy)
      · by_cases h : G.Adj v y
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨hy, h⟩
    have hdisjoint : Disjoint (insert v (G.neighborFinset v)) B := by
      apply Finset.disjoint_left.mpr
      intro y hy hb
      have h := (mem_filter.mp hb).2
      rcases mem_insert.mp hy with he | he
      · exact h.1 he
      · exact h.2 ((mem_neighborFinset _ _ _).mp he)
    have hh := card_union_of_disjoint hdisjoint
    rw [hcover, card_univ, card_insert_of_notMem (G.notMem_neighborFinset_self v),
      card_neighborFinset_eq_degree] at hh
    omega
  have hresidual : D.edgeFinset.card + G.degree v = G.edgeFinset.card := by
    have hle := G.degree_le_card_edgeFinset (v := v)
    have h := G.card_edgeFinset_deleteIncidenceSet v
    change D.edgeFinset.card = _ at h
    omega
  have hupper : D.edgeFinset.card ≤ B.card + 6 := by omega
  have hsum : 6 * B.card ≤ 2 * D.edgeFinset.card := by
    have hs : ∑ x ∈ B, D.degree x = 6 * B.card := by
      calc
        _ = ∑ _x ∈ B, 6 := sum_congr rfl (fun x hx => hDdegree x hx)
        _ = _ := by simp [Nat.mul_comm]
    have hl : ∑ x ∈ B, D.degree x ≤ ∑ x : V, D.degree x :=
      sum_le_sum_of_subset (subset_univ B)
    rw [hs, D.sum_degrees_eq_twice_card_edges] at hl
    exact hl
  have hk : B.card ≤ 3 := by omega
  have hsmall : B.card ≤ 1 := by
    by_contra hn
    have ht : 1 < B.card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp ht
    have hinter : (D.incidenceFinset x ∩ D.incidenceFinset y).card ≤ 1 := by
      calc
        _ ≤ ({s(x, y)} : Finset (Sym2 V)).card := card_le_card (by
          intro e he
          apply mem_singleton.mpr
          exact Set.mem_singleton_iff.mp
            (D.incidenceSet_inter_incidenceSet_subset hxy
              ⟨SimpleGraph.mem_incidenceFinset.mp (mem_inter.mp he).1,
                SimpleGraph.mem_incidenceFinset.mp (mem_inter.mp he).2⟩))
        _ = 1 := card_singleton _
    have hunion : (D.incidenceFinset x ∪ D.incidenceFinset y).card ≤ D.edgeFinset.card :=
      card_le_card (union_subset (D.incidenceFinset_subset x) (D.incidenceFinset_subset y))
    have hh := card_union_add_card_inter (D.incidenceFinset x) (D.incidenceFinset y)
    rw [card_incidenceFinset_eq_degree, card_incidenceFinset_eq_degree,
      hDdegree x hx, hDdegree y hy] at hh
    omega
  have hBempty : B = ∅ := by
    by_contra hn
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hn
    obtain ⟨f, hc, hp, hold, hneigh⟩ := hstructure x hx
    have hxv : x ≠ v := (mem_filter.mp hx).2.1
    have hvx : ¬G.Adj v x := (mem_filter.mp hx).2.2
    have hspoke : ∀ z : Fin 3 × Bool, G.Adj x (f (.inr (.inr z))) := by
      intro z
      simpa only [hc] using (hold (.inl ()) (.inr (.inr z))
        (by simp) (by simp) (by trivial))
    have havoidv : ∀ z : Fin 3 × Bool, f (.inr (.inr z)) ≠ v := by
      intro z he
      exact hvx (he ▸ (hspoke z).symm)
    have havoidx : ∀ z : Fin 3 × Bool, f (.inr (.inr z)) ≠ x := by
      intro z he
      have h := f.injective (he.trans hc.symm)
      simp at h
    let P : Finset (Sym2 V) := univ.image
      (fun i : Fin 3 => s(f (.inr (.inr (i, false))), f (.inr (.inr (i, true)))))
    have hPcard : P.card = 3 := by
      dsimp only [P]
      rw [card_image_of_injective _ (by
        intro i j he
        rcases Sym2.eq_iff.mp he with h | h
        · simpa using f.injective h.1
        · have hh := f.injective h.1
          simp at hh)]
      simp
    have hPsubset : P ⊆ D.edgeFinset := by
      intro e he
      obtain ⟨i, _, rfl⟩ := mem_image.mp he
      apply (mem_edgeFinset (G := D)).mpr
      change D.Adj _ _
      apply deleteIncidenceSet_adj.mpr
      exact ⟨hold _ _ (by simp) (by simp) (by simp [H]),
        havoidv _, havoidv _⟩
    have hPdisjoint : Disjoint (D.incidenceFinset x) P := by
      apply Finset.disjoint_left.mpr
      intro e hi he
      obtain ⟨i, _, rfl⟩ := mem_image.mp he
      have hm := (SimpleGraph.mem_incidenceFinset.mp hi).2
      simp only [Sym2.mem_iff] at hm
      rcases hm with hm | hm
      · exact havoidx _ hm.symm
      · exact havoidx _ hm.symm
    have hl := card_le_card (union_subset (D.incidenceFinset_subset x) hPsubset)
    rw [card_union_of_disjoint hPdisjoint, card_incidenceFinset_eq_degree,
      hDdegree x hx, hPcard] at hl
    omega
  intro x hvx
  by_contra hn
  have : x ∈ B := mem_filter.mpr ⟨mem_univ _, hvx.symm, hn⟩
  simp [hBempty] at this

#print axioms leaf_neighbor_isUniversal

end D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality
