/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLarge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphLarge
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Incident-edge coordinates specialize the strict counting bound to large cubic graphs. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphUnion
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphEvents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLarge

open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphUnion
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphMarkedEvents
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphEvents
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphArithmetic
open Finset

private theorem image_triple {E : Type} [DecidableEq E] (a b c : E) :
    univ.image (![a,b,c] : Fin 3 → E) = {a,b,c} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

private theorem incidence_triple {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 3) (v : V) :
    ∃ a b c : G.edgeSet, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.incidenceFinset v = {a.val,b.val,c.val} := by
  obtain ⟨a,b,c,hab,hac,hbc,hs⟩ := Finset.card_eq_three.mp
    ((G.card_incidenceFinset_eq_degree v).trans (hdeg v))
  have ha : a ∈ G.edgeSet := G.incidenceSet_subset v (SimpleGraph.mem_incidenceFinset.mp (by simp [hs]))
  have hb : b ∈ G.edgeSet := G.incidenceSet_subset v (SimpleGraph.mem_incidenceFinset.mp (by simp [hs]))
  have hc : c ∈ G.edgeSet := G.incidenceSet_subset v (SimpleGraph.mem_incidenceFinset.mp (by simp [hs]))
  refine ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,?_,?_,?_,hs⟩
  · exact fun h => hab (congrArg Subtype.val h)
  · exact fun h => hac (congrArg Subtype.val h)
  · exact fun h => hbc (congrArg Subtype.val h)

private theorem incidence_triple_marked {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 3)
    (v : V) (p : G.edgeSet) (hp : p.val ∈ G.incidenceFinset v) :
    ∃ a b : G.edgeSet, p ≠ a ∧ p ≠ b ∧ a ≠ b ∧
      G.incidenceFinset v = {p.val,a.val,b.val} := by
  have hs : ((G.incidenceFinset v).erase p.val).card = 2 := by
    rw [Finset.card_erase_of_mem hp, G.card_incidenceFinset_eq_degree, hdeg]
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hs
  have ham : a ∈ (G.incidenceFinset v).erase p.val := by rw [hs]; simp
  have hbm : b ∈ (G.incidenceFinset v).erase p.val := by rw [hs]; simp
  have ha : a ∈ G.edgeSet := G.incidenceSet_subset v
    (SimpleGraph.mem_incidenceFinset.mp (Finset.mem_erase.mp ham).2)
  have hb : b ∈ G.edgeSet := G.incidenceSet_subset v
    (SimpleGraph.mem_incidenceFinset.mp (Finset.mem_erase.mp hbm).2)
  refine ⟨⟨a,ha⟩,⟨b,hb⟩,?_,?_,?_,?_⟩
  · exact fun h => (Finset.mem_erase.mp ham).1 (congrArg Subtype.val h).symm
  · exact fun h => (Finset.mem_erase.mp hbm).1 (congrArg Subtype.val h).symm
  · exact fun h => hab (congrArg Subtype.val h)
  · rw [← Finset.insert_erase hp, hs]

private theorem incident_endpoints {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (p : G.edgeSet)
    (hp : p.val ∈ G.incidenceFinset v) :
    ∃ u, G.Adj v u ∧ p.val = s(v,u) := by
  have hv : v ∈ p.val := (G.edge_mem_incidenceSet_iff).mp (SimpleGraph.mem_incidenceFinset.mp hp)
  refine ⟨Sym2.Mem.other hv,?_,(Sym2.other_spec hv).symm⟩
  have he := p.property
  rw [← Sym2.other_spec hv] at he
  exact G.mem_edgeSet.mp he

set_option maxHeartbeats 1200000 in
/-- Every cubic graph with at least twelve edges has an exact AR-labeling. -/
theorem ar_graph_large {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 3)
    (hm12 : 12 ≤ G.edgeFinset.card) : IsARGraph G := by
  classical
  let m := G.edgeFinset.card
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hcard : Fintype.card G.edgeSet = m := by simp [m,SimpleGraph.edgeFinset]
  have hrel : 3 * Fintype.card V = 2 * m := cubic_card_identity G hdeg
  have hpos : 0 < Fintype.card V := by dsimp [m] at hrel; omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨p,q,r,hpq,hpr,hqr,hvinc⟩ := incidence_triple G hdeg v
  have hpv : p.val ∈ G.incidenceFinset v := by simp [hvinc]
  have hqv : q.val ∈ G.incidenceFinset v := by simp [hvinc]
  obtain ⟨u,hvuadj,hpe⟩ := incident_endpoints G v p hpv
  obtain ⟨w,hvwadj,hqe⟩ := incident_endpoints G v q hqv
  have hvu : v ≠ u := hvuadj.ne
  have hvw : v ≠ w := hvwadj.ne
  have huw : u ≠ w := by
    intro h
    apply hpq
    apply Subtype.ext
    simpa [hpe,hqe,h]
  have hpu : p.val ∈ G.incidenceFinset u := by
    rw [hpe, G.mem_incidenceFinset, G.mk'_mem_incidenceSet_right_iff]
    exact hvuadj
  have hqw : q.val ∈ G.incidenceFinset w := by
    rw [hqe, G.mem_incidenceFinset, G.mk'_mem_incidenceSet_right_iff]
    exact hvwadj
  obtain ⟨a,b,hpa,hpb,hab,huinc⟩ := incidence_triple_marked G hdeg u p hpu
  obtain ⟨c,d,hqc,hqd,hcd,hwinc⟩ := incidence_triple_marked G hdeg w q hqw
  have edge_ne (x : V) (s e : G.edgeSet) (he : e.val ∈ G.incidenceFinset x)
      (hn : s.val ∉ G.incidenceFinset x) : s ≠ e := by
    intro h
    exact hn (h.symm ▸ he)
  have hqnot : q.val ∉ G.incidenceFinset u := by
    rw [hqe, G.mem_incidenceFinset, G.mk'_mem_incidenceSet_iff]
    simp [hvu.symm,huw]
  have hpnot : p.val ∉ G.incidenceFinset w := by
    rw [hpe, G.mem_incidenceFinset, G.mk'_mem_incidenceSet_iff]
    simp [hvw.symm,huw.symm]
  have hqa : q ≠ a := edge_ne u q a (by simp [huinc]) hqnot
  have hqb : q ≠ b := edge_ne u q b (by simp [huinc]) hqnot
  have hpc : p ≠ c := edge_ne w p c (by simp [hwinc]) hpnot
  have hpd : p ≠ d := edge_ne w p d (by simp [hwinc]) hpnot
  choose A B C hAB hAC hBC hbase using incidence_triple G hdeg
  let t : V → Fin 3 → G.edgeSet := fun x =>
    if x = v then ![p,q,r] else if x = u then ![p,a,b]
    else if x = w then ![q,c,d] else ![A x,B x,C x]
  have htv : t v = ![p,q,r] := by simp [t]
  have htu : t u = ![p,a,b] := by simp [t,hvu.symm]
  have htw : t w = ![q,c,d] := by simp [t,hvw.symm,huw.symm]
  have hinc (x : V) : G.incidenceFinset x = univ.image (fun i => (t x i).val) := by
    by_cases hxv : x = v
    · subst x
      rw [htv]
      change G.incidenceFinset v = univ.image (![p.val,q.val,r.val] : Fin 3 → Sym2 V)
      rw [image_triple]
      exact hvinc
    by_cases hxu : x = u
    · subst x
      rw [htu]
      change G.incidenceFinset u = univ.image (![p.val,a.val,b.val] : Fin 3 → Sym2 V)
      rw [image_triple]
      exact huinc
    by_cases hxw : x = w
    · subst x
      rw [htw]
      change G.incidenceFinset w = univ.image (![q.val,c.val,d.val] : Fin 3 → Sym2 V)
      rw [image_triple]
      exact hwinc
    · simp only [t,if_neg hxv,if_neg hxu,if_neg hxw]
      change G.incidenceFinset x = univ.image (![(A x).val,(B x).val,(C x).val] : Fin 3 → Sym2 V)
      rw [image_triple]
      exact hbase x
  have htinj (x : V) : Function.Injective (t x) := by
    have hc : (univ.image (fun i => (t x i).val)).card = (univ : Finset (Fin 3)).card := by
      rw [← hinc x, G.card_incidenceFinset_eq_degree, hdeg]
      simp
    have hi := Finset.card_image_iff.mp hc
    intro i j hij
    apply hi (by simp) (by simp)
    exact congrArg Subtype.val hij
  let bcount (x : V) := Nat.card {e : MarkedLabeling G.edgeSet m hm p q //
    AdditiveTriple (markLabel e) (t x 0) (t x 1) (t x 2)}
  apply arGraph_of_bad_sum_lt G hm p q hpq t hinc hdeg
  apply sum_bad_card_lt m hm12 hrel v u w hvu hvw huw bcount
  · dsimp [bcount]
    simp only [htv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one]
    rw [Nat.card_eq_fintype_card]
    exact le_of_eq (card_bad_both_marked m hm (by omega) p q r hpq hpr hqr hcard)
  · dsimp [bcount]
    simp only [htu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one]
    rw [Nat.card_eq_fintype_card]
    simpa [Nat.sub_sub] using card_bad_single_marked_le m hm (by omega)
      p q p a b hpq hpa hpb hqa hqb hab hcard 1 (by omega) (by
        intro e; simp [markLabel,e.property.1])
  · dsimp [bcount]
    simp only [htw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one]
    rw [Nat.card_eq_fintype_card]
    simpa [Nat.sub_sub] using card_bad_single_marked_le m hm (by omega)
      p q q c d hpq hpc hpd hqc hqd hcd hcard 2 (by omega) (by
        intro e; simp [markLabel,e.property.2])
  · intro x hxv hxu hxw
    have htmem (i : Fin 3) : (t x i).val ∈ G.incidenceFinset x := by
      rw [hinc]
      exact Finset.mem_image.mpr ⟨i,by simp,rfl⟩
    have htp (i : Fin 3) : t x i ≠ p := by
      intro h
      have he := htmem i
      rw [h,hpe,G.mem_incidenceFinset,G.mk'_mem_incidenceSet_iff] at he
      exact (by simpa [hxv,hxu] using he : False)
    have htq (i : Fin 3) : t x i ≠ q := by
      intro h
      have he := htmem i
      rw [h,hqe,G.mem_incidenceFinset,G.mk'_mem_incidenceSet_iff] at he
      exact (by simpa [hxv,hxw] using he : False)
    dsimp [bcount]
    rw [Nat.card_eq_fintype_card]
    exact card_bad_free_triple m (by omega) hm p q hpq (t x) (htinj x) htp htq hcard

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLarge
