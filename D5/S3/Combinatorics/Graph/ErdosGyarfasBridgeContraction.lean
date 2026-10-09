/- GID: D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bridge contraction preserves bipartiteness, minimum degree, and cycle lengths. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Card

namespace D5.S3.Combinatorics.Graph.ErdosGyarfasBridgeContraction

open SimpleGraph

private lemma walk_side_constant {V : Type} {G : SimpleGraph V} (a : V) (side : V → Prop)
    (hedge : ∀ x y, G.Adj x y → x ≠ a → y ≠ a → (side x ↔ side y))
    {x y : V} (p : G.Walk x y) (ha : ∀ z ∈ p.support, z ≠ a) :
    ∀ z ∈ p.support, side z ↔ side x := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · rfl
    · have ht : ∀ t ∈ p.support, t ≠ a := fun t ht => ha t (by simp [ht])
      exact (ih ht w hw).trans (hedge x y h (ha x (by simp)) (ht y p.start_mem_support)).symm

private lemma cycle_center_side {V : Type} {G : SimpleGraph V} (a : V) (side : V → Prop)
    (hedge : ∀ x y, G.Adj x y → x ≠ a → y ≠ a → (side x ↔ side y))
    (p : G.Walk a a) (hp : p.IsCycle) :
    ∀ z ∈ p.support, z ≠ a → (side z ↔ side p.snd) := by
  have ht : ¬p.tail.Nil := by
    have hl := hp.three_le_length
    intro h
    have hz : p.tail.length = 0 := (Walk.length_eq_zero_iff).mpr h
    rw [Walk.length_tail] at hz
    omega
  have hconcat := p.tail.support_dropLast_concat ht
  have hnodup : (p.tail.dropLast.support ++ [a]).Nodup := by
    rw [hconcat, p.support_tail_of_not_nil hp.not_nil]
    exact hp.support_nodup
  have havoid : ∀ z ∈ p.tail.dropLast.support, z ≠ a := by
    intro z hz hza
    subst z
    exact (List.disjoint_of_nodup_append hnodup) hz (by simp)
  have hsupport : p.support = a :: (p.tail.dropLast.support ++ [a]) := by
    rw [hconcat]
    exact (p.cons_support_tail hp.not_nil).symm
  intro z hz hza
  have hz' : z ∈ p.tail.dropLast.support := by
    rw [hsupport] at hz
    simp only [List.mem_cons, List.mem_append] at hz
    tauto
  exact walk_side_constant a side hedge p.tail.dropLast havoid z hz'

lemma cycle_side_confinement {V : Type} {G : SimpleGraph V} (a : V) (side : V → Prop)
    (hedge : ∀ x y, G.Adj x y → x ≠ a → y ≠ a → (side x ↔ side y))
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    (∀ x ∈ p.support, x = a ∨ side x) ∨ (∀ x ∈ p.support, x = a ∨ ¬side x) := by
  classical
  by_cases ha : a ∈ p.support
  · let q := p.rotate a ha
    have hq : q.IsCycle := hp.rotate ha
    have hs := cycle_center_side a side hedge q hq
    by_cases hside : side q.snd
    · left
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr ((hs x ((p.mem_support_rotate_iff a ha).mpr hx) hxa).mpr hside)
    · right
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr (fun h => hside ((hs x ((p.mem_support_rotate_iff a ha).mpr hx) hxa).mp h))
  · have havoid : ∀ x ∈ p.support, x ≠ a := by
      intro x hx hxa
      subst x
      exact ha hx
    have hs := walk_side_constant a side hedge p havoid
    by_cases hside : side v
    · exact Or.inl (fun x hx => Or.inr ((hs x hx).mpr hside))
    · exact Or.inr (fun x hx => Or.inr (fun h => hside ((hs x hx).mp h)))


lemma lift_cycle_of_support {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (s : Set V) (f : H.induce s →g G) (hf : Function.Injective f)
    {v : V} (p : H.Walk v v) (hp : p.IsCycle)
    (hs : ∀ x ∈ p.support, x ∈ s) :
    ∃ q : G.Walk (f ⟨v, hs v p.start_mem_support⟩) (f ⟨v, hs v p.start_mem_support⟩),
      q.IsCycle ∧ q.length = p.length := by
  let r := p.induce s hs
  have hr : r.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce s).toHom)
    simpa [r] using hp
  refine ⟨r.map f, hr.map hf, ?_⟩
  rw [Walk.length_map]
  have heq := Walk.map_induce (s := s) p hs
  exact (Walk.length_map (Embedding.induce s).toHom r).symm.trans (congrArg (fun w => w.length) heq)


variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (u v : V)

abbrev ContractVertex := {x : V // x ≠ v}

def contraction : SimpleGraph (ContractVertex v) where
  Adj x y := x ≠ y ∧ (G.Adj x.val y.val ∨
    (x.val = u ∧ G.Adj v y.val) ∨ (y.val = u ∧ G.Adj x.val v))
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, h.2.elim (fun h ↦ Or.inl h.symm)
      (fun h ↦ h.elim (fun h ↦ Or.inr (Or.inr ⟨h.1, h.2.symm⟩))
        (fun h ↦ Or.inr (Or.inl ⟨h.1, h.2.symm⟩)))⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

noncomputable instance contractionDecidable : DecidableRel (contraction G u v).Adj :=
  fun _ _ ↦ Classical.propDecidable _

noncomputable def side (x : V) : Prop := (G.deleteEdges {s(u, v)}).Reachable u x

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma side_u : side G u v u := Reachable.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma side_adj {x y : V} (h : G.Adj x y) (he : s(x, y) ≠ s(u, v)) :
    side G u v x ↔ side G u v y := by
  have hd : (G.deleteEdges {s(u, v)}).Adj x y := deleteEdges_adj.mpr ⟨h, by simpa using he⟩
  exact ⟨fun hx ↦ hx.trans hd.reachable, fun hy ↦ hy.trans hd.symm.reachable⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma no_common_neighbor (hb : G.IsBridge s(u, v)) {x : V}
    (hux : G.Adj u x) (hvx : G.Adj v x) : False := by
  have hxv : x ≠ v := hvx.ne.symm
  have hxu : x ≠ u := hux.ne.symm
  have h1 := side_adj G u v hux (by simp [hxv, hxu])
  have h2 := side_adj G u v hvx (by simp [hxv, hxu])
  exact hb (h2.mpr (h1.mp (side_u G u v)))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma side_adj_subtype {x y : ContractVertex v} (h : G.Adj x.val y.val) :
    side G u v x.val ↔ side G u v y.val :=
  side_adj G u v h (by simp [x.property, y.property])

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma not_side_neighbor_v (hb : G.IsBridge s(u, v)) {x : V}
    (hx : x ≠ u) (h : G.Adj v x) : ¬ side G u v x := by
  have he : s(v,x) ≠ s(u, v) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨hvu,hxv⟩ | ⟨_,hxu⟩
    · exact h.ne hxv.symm
    · exact hx hxu
  exact fun hside ↦ hb ((side_adj G u v h he).mpr hside)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma contraction_colorable (hb : G.IsBridge s(u, v)) (hc : G.Colorable 2) :
    (contraction G u v).Colorable 2 := by
  classical
  obtain ⟨c⟩ := hc
  let flip := Equiv.swap (c u) (c v)
  let f : ContractVertex v → Fin 2 := fun x ↦ if side G u v x.val then c x.val else flip (c x.val)
  refine ⟨Coloring.mk f ?_⟩
  intro x y h
  rcases h with ⟨hne,hxy | ⟨hxu,hvy⟩ | ⟨hyu,hxv⟩⟩
  · have hs := side_adj_subtype G u v hxy
    by_cases hx : side G u v x.val
    · have hy := hs.mp hx
      simpa [f,hx,hy] using c.valid hxy
    · have hy : ¬side G u v y.val := fun hy ↦ hx (hs.mpr hy)
      simpa [f,hx,hy] using flip.injective.ne (c.valid hxy)
  · have hyu : y.val ≠ u := by intro h; apply hne; exact Subtype.ext (hxu.trans h.symm)
    have hy := not_side_neighbor_v G u v hb hyu hvy
    have hx : side G u v x.val := hxu ▸ side_u G u v
    have hv : flip (c v) = c u := Equiv.swap_apply_right _ _
    have hh : c u ≠ flip (c y.val) := by
      rw [← hv]
      exact flip.injective.ne (c.valid hvy)
    simpa [f,hx,hy,hxu,side_u] using hh
  · have hxu : x.val ≠ u := by intro h; apply hne; exact Subtype.ext (h.trans hyu.symm)
    have hx := not_side_neighbor_v G u v hb hxu hxv.symm
    have hy : side G u v y.val := hyu ▸ side_u G u v
    have hv : flip (c v) = c u := Equiv.swap_apply_right _ _
    have hh : flip (c x.val) ≠ c u := by
      rw [← hv]
      exact flip.injective.ne (c.valid hxv)
    simpa [f,hx,hy,hyu,side_u] using hh

lemma contraction_card_lt : Fintype.card (ContractVertex v) < Fintype.card V :=
  Fintype.card_subtype_lt (x := v) (by simp)

private def q (huv : u ≠ v) (y : V) : {x : V // x ≠ v} :=
  if h : y = v then ⟨u, huv⟩ else ⟨y, h⟩
omit [Fintype V] in
private theorem q_val (huv : u ≠ v) (y : V) : (q u v huv y).val = if y=v then u else y := by
  simp [q]; split_ifs <;> rfl
private lemma degree_contraction_aux (huv : u ≠ v) (H : SimpleGraph {x : V // x ≠ v})
    [DecidableRel H.Adj]
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ (G.Adj x.val y.val ∨
      (x.val = u ∧ G.Adj v y.val) ∨ (y.val = u ∧ G.Adj x.val v)))
    (hc : ∀ z, ¬ (G.Adj u z ∧ G.Adj v z))
    (hadj : G.Adj u v) (hd : ∀ z, 3 ≤ G.degree z) :
    ∀ x, 3 ≤ H.degree x := by
  classical
  intro x
  by_cases hxu : x.val = u
  · let s := (G.neighborFinset u).erase v ∪ (G.neighborFinset v).erase u
    have hs : ∀ y ∈ s, y ≠ v := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (Finset.mem_erase.mp hy).1
      · have h := (Finset.mem_erase.mp hy).2
        have hy' : G.Adj v y := (G.mem_neighborFinset v y).mp h
        exact hy'.ne.symm
    have hm : Set.MapsTo (q u v huv) (s : Set V) (H.neighborFinset x : Set _) := by
      intro y hy
      apply (H.mem_neighborFinset x _).mpr
      apply (hH _ _).mpr
      constructor
      · intro heq
        have hval := congrArg Subtype.val heq
        have hq : (q u v huv y).val = y := by simp [q_val, hs y hy]
        rw [hxu, hq] at hval
        rcases Finset.mem_union.mp hy with hy | hy
        · exact ((G.mem_neighborFinset u y).mp (Finset.mem_erase.mp hy).2).ne hval
        · exact (Finset.mem_erase.mp hy).1 hval.symm
      have hq : (q u v huv y).val = y := by simp [q_val, hs y hy]
      rw [hq, hxu]
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Or.inl ((G.mem_neighborFinset u y).mp (Finset.mem_erase.mp hy).2)
      · exact Or.inr (Or.inl ⟨rfl, (G.mem_neighborFinset v y).mp (Finset.mem_erase.mp hy).2⟩)
    have hi : Set.InjOn (q u v huv) (s : Set V) := by
      intro a ha b hb hab
      have hh := congrArg Subtype.val hab
      simpa [q_val, hs a ha, hs b hb] using hh
    have hle := Finset.card_le_card_of_injOn (q u v huv) hm hi
    have hj : Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact hc y ⟨(G.mem_neighborFinset u y).mp (Finset.mem_erase.mp hy).2,
        (G.mem_neighborFinset v y).mp (Finset.mem_erase.mp hz).2⟩
    have hsu := Finset.card_erase_add_one ((G.mem_neighborFinset u v).mpr hadj)
    have hsv := Finset.card_erase_add_one ((G.mem_neighborFinset v u).mpr hadj.symm)
    have hsc : s.card = ((G.neighborFinset u).erase v).card +
        ((G.neighborFinset v).erase u).card := Finset.card_union_of_disjoint hj
    rw [G.card_neighborFinset_eq_degree] at hsu hsv
    rw [H.card_neighborFinset_eq_degree] at hle
    have hu := hd u
    have hv := hd v
    omega
  · have hm : Set.MapsTo (q u v huv) (G.neighborFinset x.val : Set V)
        (H.neighborFinset x : Set _) := by
      intro y hy
      have hadjxy := (G.mem_neighborFinset x.val y).mp hy
      apply (H.mem_neighborFinset x _).mpr
      apply (hH _ _).mpr
      constructor
      · intro heq
        have hval := congrArg Subtype.val heq
        by_cases hyv : y = v
        · exact hxu (by simpa [q_val, hyv] using hval)
        · exact hadjxy.ne (by simpa [q_val, hyv] using hval)
      by_cases hy : y = v
      · right; right
        refine ⟨by simp [q_val, hy], ?_⟩
        simpa [hy] using hadjxy
      · left
        simpa [q_val, hy] using hadjxy
    have hi : Set.InjOn (q u v huv) (G.neighborFinset x.val : Set V) := by
      intro a ha b hb hab
      have hh := congrArg Subtype.val hab
      have hxa := (G.mem_neighborFinset x.val a).mp ha
      have hxb := (G.mem_neighborFinset x.val b).mp hb
      by_cases hav : a = v <;> by_cases hbv : b = v
      · exact hav.trans hbv.symm
      · have hbu : b = u := by simpa [q_val, hav, hbv] using hh.symm
        exact False.elim (hc x.val ⟨(hbu ▸ hxb).symm, (hav ▸ hxa).symm⟩)
      · have hau : a = u := by simpa [q_val, hav, hbv] using hh
        exact False.elim (hc x.val ⟨(hau ▸ hxa).symm, (hbv ▸ hxb).symm⟩)
      · simpa [q_val, hav, hbv] using hh
    have hle := Finset.card_le_card_of_injOn (q u v huv) hm hi
    rw [G.card_neighborFinset_eq_degree, H.card_neighborFinset_eq_degree] at hle
    exact (hd _).trans hle

lemma contraction_min_degree (hb : G.IsBridge s(u, v))
    (hadj : G.Adj u v) (hd : ∀ z, 3 ≤ G.degree z) :
    ∀ x, 3 ≤ (contraction G u v).degree x := by
  classical
  exact degree_contraction_aux G u v hadj.ne (contraction G u v)
    (fun _ _ ↦ Iff.rfl) (fun z hz ↦ no_common_neighbor G u v hb hz.1 hz.2) hadj hd

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma contraction_cycle_lift (huv : u ≠ v) (hb : G.IsBridge s(u, v))
    {w : ContractVertex v} (p : (contraction G u v).Walk w w) (hp : p.IsCycle) :
    ∃ (z : V) (q : G.Walk z z), q.IsCycle ∧ q.length = p.length := by
  classical
  let a : ContractVertex v := ⟨u,huv⟩
  have hedge : ∀ x y, (contraction G u v).Adj x y → x ≠ a → y ≠ a →
      (side G u v x.val ↔ side G u v y.val) := by
    intro x y h hx hy
    have hxu : x.val ≠ u := fun hh ↦ hx (Subtype.ext hh)
    have hyu : y.val ≠ u := fun hh ↦ hy (Subtype.ext hh)
    rcases h.2 with h | h | h
    · exact side_adj_subtype G u v h
    · exact False.elim (hxu h.1)
    · exact False.elim (hyu h.1)
  obtain hs | hs := cycle_side_confinement a (fun x ↦ side G u v x.val) hedge p hp
  · let S : Set (ContractVertex v) := {x | side G u v x.val}
    have hS : ∀ x ∈ p.support, x ∈ S := by
      intro x hx
      rcases hs x hx with h | h
      · subst x; exact side_u G u v
      · exact h
    let f : (contraction G u v).induce S →g G := {
      toFun := fun x ↦ x.val.val
      map_rel' := by
        intro x y h
        rcases h.2 with h | ⟨hxu,hvy⟩ | ⟨hyu,hxv⟩
        · exact h
        · have hyu : y.val.val ≠ u := by
            intro hh; exact h.1 (Subtype.ext (hxu.trans hh.symm))
          exact False.elim (not_side_neighbor_v G u v hb hyu hvy y.property)
        · have hxu : x.val.val ≠ u := by
            intro hh; exact h.1 (Subtype.ext (hh.trans hyu.symm))
          exact False.elim (not_side_neighbor_v G u v hb hxu hxv.symm x.property) }
    have hf : Function.Injective f := fun x y h ↦ Subtype.ext (Subtype.ext h)
    obtain ⟨q,hq,hl⟩ := lift_cycle_of_support S f hf p hp hS
    exact ⟨_,q,hq,hl⟩
  · let S : Set (ContractVertex v) := {x | x.val = u ∨ ¬side G u v x.val}
    have hS : ∀ x ∈ p.support, x ∈ S := by
      intro x hx
      rcases hs x hx with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr h
    let fval : S → V := fun x ↦ if x.val.val = u then v else x.val.val
    have ffix : ∀ x : S, x.val.val ≠ u → fval x = x.val.val := by
      intro x hx; simp [fval,hx]
    have fu : ∀ x : S, x.val.val = u → fval x = v := by
      intro x hx; simp [fval,hx]
    let f : (contraction G u v).induce S →g G := {
      toFun := fval
      map_rel' := by
        intro x y h
        by_cases hx : x.val.val = u
        · have hy : y.val.val ≠ u := by intro hh; exact h.1 (Subtype.ext (hx.trans hh.symm))
          rw [fu x hx,ffix y hy]
          rcases h.2 with hxy | ⟨_,hvy⟩ | ⟨hyu,_⟩
          · have hyside : side G u v y.val.val :=
              (side_adj_subtype G u v hxy).mp (hx ▸ side_u G u v)
            rcases y.property with hyu | hy'
            · exact False.elim (hy hyu)
            · exact False.elim (hy' hyside)
          · exact hvy
          · exact False.elim (hy hyu)
        · by_cases hy : y.val.val = u
          · rw [ffix x hx,fu y hy]
            rcases h.2 with hxy | ⟨hxu,_⟩ | ⟨_,hxv⟩
            · have hxside : side G u v x.val.val :=
                (side_adj_subtype G u v hxy).mpr (hy ▸ side_u G u v)
              rcases x.property with hxu | hx'
              · exact False.elim (hx hxu)
              · exact False.elim (hx' hxside)
            · exact False.elim (hx hxu)
            · exact hxv
          · rw [ffix x hx,ffix y hy]
            rcases h.2 with hxy | ⟨hxu,_⟩ | ⟨hyu,_⟩
            · exact hxy
            · exact False.elim (hx hxu)
            · exact False.elim (hy hyu) }
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext; apply Subtype.ext
      change fval x = fval y at h
      by_cases hx : x.val.val = u <;> by_cases hy : y.val.val = u
      · exact hx.trans hy.symm
      · rw [fu x hx,ffix y hy] at h
        exact False.elim (y.val.property h.symm)
      · rw [ffix x hx,fu y hy] at h
        exact False.elim (x.val.property h)
      · rwa [ffix x hx,ffix y hy] at h
    obtain ⟨q,hq,hl⟩ := lift_cycle_of_support S f hf p hp hS
    exact ⟨_,q,hq,hl⟩

end D5.S3.Combinatorics.Graph.ErdosGyarfasBridgeContraction
