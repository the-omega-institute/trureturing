/- GID: D5/S3/Combinatorics/Graph/LinearForests/OrientationFibers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/OrientationFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Actual full-cycle permutations over labelled undirected cycles. -/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
namespace D5.S3.Combinatorics.Graph.LinearForests.OrientationFibers
open SimpleGraph Equiv
open scoped Classical

variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem walk_permutation {C : SimpleGraph V} {a : V}
    (p : C.Walk a a) (hp : p.IsCycle) (hall : ∀ v, v ∈ p.support) :
    ∃ σ : Perm V, σ.IsCycleOn Set.univ ∧
      ∀ d : C.Dart, d ∈ p.darts ↔ σ d.fst = d.snd := by
  classical
  let l := p.support.dropLast
  have hn : l.Nodup := hp.nodup_dropLast_support
  have hl : l.length = p.length := by simp [l]
  have hm (v : V) : v ∈ l := by
    apply p.tail_support_perm_dropLast_support.mem_iff.mp
    have hv := hall v
    rw [← p.cons_tail_support, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact p.end_mem_tail_support hp.not_nil
    · exact hv
  have hnext (i : ℕ) (hi : i < p.length) :
      l.formPerm (p.getVert i) = p.getVert (i + 1) := by
    have h := List.formPerm_apply_getElem l hn i (by omega)
    have hget (j : ℕ) (hj : j < p.length) :
        l[j]'(by omega) = p.getVert j := by
      simp only [l, List.getElem_dropLast]
      exact p.support_getElem_eq_getVert _
    rw [hget i hi] at h
    by_cases hj : i + 1 < p.length
    · simpa only [hl, Nat.mod_eq_of_lt hj, hget (i + 1) hj] using h
    · have he : i + 1 = p.length := by omega
      simpa only [hl, he, Nat.mod_self, hget 0 (by omega),
        Walk.getVert_zero, Walk.getVert_length] using h
  have hd (d : C.Dart) (h : d ∈ p.darts) : l.formPerm d.fst = d.snd := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    rw [Walk.darts_getElem_eq_getVert]
    exact hnext i (by simpa using hi)
  have hcy : l.formPerm.IsCycle := List.isCycle_formPerm hn (by have := hp.three_le_length; omega)
  have hs : {v | l.formPerm v ≠ v} = Set.univ := by
    have h := List.support_formPerm_of_nodup' l hn (by
      intro v hv
      have := hp.three_le_length
      have : l.length = 1 := by rw [hv]; rfl
      omega)
    rw [h]
    ext v
    simp [hm v]
  refine ⟨l.formPerm, hs ▸ hcy.isCycleOn, fun d => ⟨hd d, fun h => ?_⟩⟩
  obtain ⟨e, he, hef⟩ := List.mem_map.mp (show d.fst ∈ p.darts.map (·.fst) by
    rw [p.map_fst_darts]
    exact hm d.fst)
  have hes : e.snd = d.snd := (hd e he).symm.trans (hef ▸ h)
  have hed : e = d := Dart.ext _ _ (Prod.ext hef hes)
  exact hed ▸ he

private theorem raw_cycle_permutation (C : SimpleGraph V) [DecidableRel C.Adj]
    (hc : C.Connected) (hd : ∀ v, C.degree v = 2) :
    ∃ σ : Perm V, σ.IsCycleOn Set.univ ∧
      ∀ x y, C.Adj x y ↔ σ x = y ∨ σ y = x := by
  classical
  have hcycles : C.IsCycles := by
    intro v _
    simpa only [Set.ncard_eq_toFinset_card', ← C.neighborFinset_def,
      C.card_neighborFinset_eq_degree] using hd v
  obtain ⟨a⟩ := hc.nonempty
  have hne : (C.neighborSet a).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    simpa only [Set.ncard_eq_toFinset_card', ← C.neighborFinset_def,
      C.card_neighborFinset_eq_degree, hd] using (by decide : 2 ≠ 0))
  obtain ⟨p, hp, hverts⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C.connectedComponentMk a) (by simp [ConnectedComponent.mem_supp_iff]) hne
  have hall (v : V) : v ∈ p.support := by
    rw [← Walk.mem_verts_toSubgraph, hverts, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact hc v a
  obtain ⟨σ, hσ, hσd⟩ := walk_permutation p hp hall
  refine ⟨σ, hσ, fun x y => ?_⟩
  constructor
  · intro h
    have he : s(x,y) ∈ p.edges := by
      exact Walk.adj_toSubgraph_iff_mem_edges.mp
        ((hp.adj_toSubgraph_iff_of_isCycles hcycles
          (p.mem_verts_toSubgraph.mpr (hall x)) y).mpr h)
    rw [p.edges_eq_map_darts] at he
    obtain ⟨d, hd, he⟩ := List.mem_map.mp he
    change s(d.fst,d.snd) = s(x,y) at he
    have hh := (Sym2.eq_iff).mp he
    rcases hh with hh | hh
    · left
      have h := (hσd d).mp hd
      rcases hh with ⟨hx,hy⟩
      simpa only [hx,hy] using h
    · right
      have h := (hσd d).mp hd
      rcases hh with ⟨hx,hy⟩
      simpa only [hx,hy] using h
  · rintro (h | h)
    · obtain ⟨d, hd, hdx⟩ := List.mem_map.mp (show x ∈ p.darts.map (·.fst) by
        rw [p.map_fst_darts]
        apply p.tail_support_perm_dropLast_support.mem_iff.mp
        have hv := hall x
        rw [← p.cons_tail_support, List.mem_cons] at hv
        exact hv.elim (fun e => e ▸ p.end_mem_tail_support hp.not_nil) id)
      have hdy : d.snd = y := ((hσd d).mp hd).symm.trans (hdx ▸ h)
      simpa only [hdx, hdy] using d.adj
    · exact C.adj_symm (by
        obtain ⟨d, hd, hdy⟩ := List.mem_map.mp (show y ∈ p.darts.map (·.fst) by
          rw [p.map_fst_darts]
          apply p.tail_support_perm_dropLast_support.mem_iff.mp
          have hv := hall y
          rw [← p.cons_tail_support, List.mem_cons] at hv
          exact hv.elim (fun e => e ▸ p.end_mem_tail_support hp.not_nil) id)
        have hdx : d.snd = x := ((hσd d).mp hd).symm.trans (hdy ▸ h)
        simpa only [hdy, hdx] using d.adj)

private theorem no_short_cycle (hn : 3 ≤ Fintype.card V) (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) (v : V) : σ v ≠ v ∧ σ (σ v) ≠ v := by
  have hf : σ.IsCycleOn (↑(Finset.univ : Finset V)) := by simpa using hσ
  constructor
  · intro h
    have hh := (hf.pow_apply_eq (Finset.mem_univ v) (n := 1)).mp (by simpa using h)
    simp only [Finset.card_univ] at hh
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hh
  · intro h
    have hh := (hf.pow_apply_eq (Finset.mem_univ v) (n := 2)).mp (by simpa [pow_two] using h)
    simp only [Finset.card_univ] at hh
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hh

private theorem permutation_faces (C : SimpleGraph V) [DecidableRel C.Adj]
    (σ : Perm V) (hshort : ∀ v, σ v ≠ v ∧ σ (σ v) ≠ v)
    (hC : ∀ x y, C.Adj x y ↔ σ x = y ∨ σ y = x) :
    ∃ (R : D5.S3.Combinatorics.Graph.PlanarMatching.Rotation C)
      (x : R.Face → ZMod 2),
      (∀ d : C.Dart, x (R.face d) = if σ d.fst = d.snd then 1 else 0) ∧
      R.boundary x = fun _ => 1 := by
  classical
  let turn (d : C.Dart) : C.Dart :=
    ⟨(d.fst, if σ d.fst = d.snd then σ⁻¹ d.fst else σ d.fst), by
      split_ifs
      · exact (hC _ _).mpr (Or.inr (σ.apply_symm_apply _))
      · exact (hC _ _).mpr (Or.inl rfl)⟩
  have hforward (d : C.Dart) : σ d.fst = (turn d).snd ↔ σ d.fst ≠ d.snd := by
    have hs := (hshort (σ⁻¹ d.fst)).2
    have hne : σ d.fst ≠ σ⁻¹ d.fst := by
      intro h
      apply hs
      change σ (σ (σ.symm d.fst)) = σ.symm d.fst
      simpa using h
    simp only [turn]
    split_ifs <;> simp_all
  have hinv : Function.Involutive turn := by
    intro d
    apply Dart.ext
    apply Prod.ext
    · rfl
    · have hd := (hC _ _).mp d.adj
      have hf := hforward d
      change (if σ d.fst = (turn d).snd then σ⁻¹ d.fst else σ d.fst) = d.snd
      by_cases h : σ d.fst = d.snd
      · rw [if_neg (fun hh => (hf.mp hh) h)]
        exact h
      · rw [if_pos (hf.mpr h)]
        apply σ.injective
        simpa using (hd.resolve_left h).symm
  let rotor : Perm C.Dart := hinv.toPerm turn
  have hrotfst (d : C.Dart) : (rotor d).fst = d.fst := rfl
  have horbit (d e : C.Dart) : rotor.SameCycle d e ↔ d.fst = e.fst := by
    constructor
    · intro h
      obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
      have hi : Function.Semiconj (fun d : C.Dart => d.fst) rotor id := hrotfst
      simpa only [Function.iterate_id, id_eq, Perm.iterate_eq_pow] using (hi.iterate_right n d).symm
    · intro he
      by_cases hde : d = e
      · exact hde.sameCycle rotor
      · have hturn : rotor d = e := by
          apply Dart.ext
          refine Prod.ext ((hrotfst d).trans he) ?_
          have hd := (hC _ _).mp d.adj
          have het := (hC _ _).mp e.adj
          have hne : d.snd ≠ e.snd := by
            intro h
            exact hde (Dart.ext _ _ (Prod.ext he h))
          change (if σ d.fst = d.snd then σ⁻¹ d.fst else σ d.fst) = e.snd
          rw [← he] at het
          split_ifs with h
          · have hh : σ e.snd = d.fst := het.resolve_left (by grind)
            apply σ.injective
            simpa using hh.symm
          · exact (het.resolve_right (by
              intro hh
              have hh' := hd.resolve_left h
              exact hne (σ.injective (hh'.trans hh.symm))))
        exact hturn ▸ (Perm.sameCycle_apply_right.mpr (.refl rotor d))
  let R : D5.S3.Combinatorics.Graph.PlanarMatching.Rotation C := ⟨rotor,horbit⟩
  let label (d : C.Dart) : ZMod 2 := if σ d.fst = d.snd then 1 else 0
  have hlabel (d : C.Dart) : label (R.facePerm d) = label d := by
    change (if σ d.snd = (turn d.symm).snd then (1 : ZMod 2) else 0) =
      (if σ d.fst = d.snd then 1 else 0)
    have hf := hforward d.symm
    have hd := (hC _ _).mp d.adj
    have he : σ d.snd = (turn d.symm).snd ↔ σ d.fst = d.snd := by
      change (σ d.snd = (turn d.symm).snd ↔ σ d.snd ≠ d.fst) at hf
      rw [hf]
      change (σ d.snd ≠ d.fst) ↔ σ d.fst = d.snd
      constructor
      · exact fun h => hd.resolve_right h
      · intro h hh
        exact (hshort d.fst).2 (by rw [h,hh])
    simp only [he]
  let x : R.Face → ZMod 2 := Quotient.lift label (by
    intro d e h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    have hi : Function.Semiconj label R.facePerm id := hlabel
    simpa only [Function.iterate_id, id_eq, Perm.iterate_eq_pow] using (hi.iterate_right n d).symm)
  have hx (d : C.Dart) : x (R.face d) = label d := rfl
  refine ⟨R,x,fun d => hx d,?_⟩
  funext e
  obtain ⟨d,hd⟩ := D5.S3.Combinatorics.Graph.PlanarMatching.Rotation.edgeRep C e
  have h := R.boundary_dart x d
  have hed : (⟨d.edge,d.edge_mem⟩ : C.edgeSet) = e := Subtype.ext hd
  rw [hed,hx,hx] at h
  rw [h]
  dsimp only [label]
  have hadj := (hC _ _).mp d.adj
  have hs := (hshort d.fst).2
  change (if σ d.fst = d.snd then (1 : ZMod 2) else 0) +
    (if σ d.snd = d.fst then 1 else 0) = 1
  rcases hadj with h | h
  · rw [if_pos h, if_neg (fun hh => hs (by rw [h,hh]))]
    simp
  · rw [if_pos h, if_neg (fun hh => hs (by rw [hh,h]))]
    simp

private theorem permutation_boundary_walk (C : SimpleGraph V) [DecidableRel C.Adj]
    {a : V} (p : C.Walk a a) (hp : p.IsCycle)
    (hedges : ∀ e : C.edgeSet, e.val ∈ p.edges)
    (σ : Perm V) (hshort : ∀ v, σ v ≠ v ∧ σ (σ v) ≠ v)
    (hC : ∀ x y, C.Adj x y ↔ σ x = y ∨ σ y = x) :
    ∃ q : C.Walk a a, (q = p ∨ q = p.reverse) ∧
      ∀ d : C.Dart, σ d.fst = d.snd ↔ d ∈ q.darts := by
  classical
  obtain ⟨R,x,hx,hb⟩ := permutation_faces C σ hshort hC
  have hb' : R.boundary x = fun e : C.edgeSet => if e.val ∈ p.edges then 1 else 0 := by
    simpa only [hedges, ite_true] using hb
  obtain ⟨q,hq,hqd⟩ := R.cycle_boundary_walk p hp x hb'
  refine ⟨q,hq,fun d => ?_⟩
  rw [← (hqd d).1, hx d, hx d.symm]
  change (σ d.fst = d.snd) ↔
    ((if σ d.fst = d.snd then (1 : ZMod 2) else 0) = 1 ∧
      (if σ d.snd = d.fst then (1 : ZMod 2) else 0) = 0)
  by_cases h : σ d.fst = d.snd
  · have hh : σ d.snd ≠ d.fst := by
      intro hh
      exact (hshort d.fst).2 (by rw [h,hh])
    simp [h,hh]
  · simp [h]

private theorem same_darts_permutation (C : SimpleGraph V) {a : V}
    (p : C.Walk a a) (hp : p.IsCycle) (hall : ∀ v, v ∈ p.support)
    (σ τ : Perm V)
    (hσ : ∀ d : C.Dart, σ d.fst = d.snd ↔ d ∈ p.darts)
    (hτ : ∀ d : C.Dart, τ d.fst = d.snd ↔ d ∈ p.darts) : σ = τ := by
  apply Perm.ext
  intro v
  have hv : v ∈ p.support.dropLast := by
    apply p.tail_support_perm_dropLast_support.mem_iff.mp
    have hv := hall v
    rw [← p.cons_tail_support, List.mem_cons] at hv
    exact hv.elim (fun e => e ▸ p.end_mem_tail_support hp.not_nil) id
  rw [← p.map_fst_darts] at hv
  obtain ⟨d,hd,hdv⟩ := List.mem_map.mp hv
  have hs := (hσ d).mpr hd
  have ht := (hτ d).mpr hd
  simpa only [hdv] using hs.trans ht.symm

private theorem actual_permutation_fiber (hn : 3 ≤ Fintype.card V)
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (hc : C.Connected) (hd : ∀ v, C.degree v = 2)
    (σ τ : Perm V) (hσ : σ.IsCycleOn Set.univ) (hτ : τ.IsCycleOn Set.univ)
    (hs : ∀ x y, C.Adj x y ↔ σ x = y ∨ σ y = x)
    (ht : ∀ x y, C.Adj x y ↔ τ x = y ∨ τ y = x) :
    τ = σ ∨ τ = σ⁻¹ := by
  classical
  have hcycles : C.IsCycles := by
    intro v _
    simpa only [Set.ncard_eq_toFinset_card', ← C.neighborFinset_def,
      C.card_neighborFinset_eq_degree] using hd v
  obtain ⟨a⟩ := hc.nonempty
  have hne : (C.neighborSet a).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    simpa only [Set.ncard_eq_toFinset_card', ← C.neighborFinset_def,
      C.card_neighborFinset_eq_degree, hd] using (by decide : 2 ≠ 0))
  obtain ⟨p,hp,hverts⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C.connectedComponentMk a) (by simp [ConnectedComponent.mem_supp_iff]) hne
  have hall (v : V) : v ∈ p.support := by
    rw [← Walk.mem_verts_toSubgraph,hverts,ConnectedComponent.mem_supp_iff,ConnectedComponent.eq]
    exact hc v a
  have hevery (e : C.edgeSet) : e.val ∈ p.edges := by
    rcases e with ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact Walk.adj_toSubgraph_iff_mem_edges.mp
        ((hp.adj_toSubgraph_iff_of_isCycles hcycles
          (p.mem_verts_toSubgraph.mpr (hall x)) y).mpr he)
  obtain ⟨q,hq,hqσ⟩ := permutation_boundary_walk C p hp hevery σ (no_short_cycle hn σ hσ) hs
  obtain ⟨r,hr,hrτ⟩ := permutation_boundary_walk C p hp hevery τ (no_short_cycle hn τ hτ) ht
  have hqcycle : q.IsCycle := by rcases hq with rfl | rfl; exact hp; exact hp.reverse
  have hqall (v : V) : v ∈ q.support := by
    rcases hq with rfl | rfl
    · exact hall v
    · simpa using hall v
  have hqr : r = q ∨ r = q.reverse := by
    rcases hq with hq | hq <;> rcases hr with hr | hr <;> simp [hq,hr]
  rcases hqr with hqr | hqr
  · rw [hqr] at hrτ
    exact Or.inl (same_darts_permutation C q hqcycle hqall τ σ hrτ hqσ)
  · right
    rw [hqr] at hrτ
    apply same_darts_permutation C q.reverse hqcycle.reverse (by simpa using hqall) τ σ⁻¹ hrτ
    intro d
    rw [Walk.mem_darts_reverse, ← hqσ d.symm]
    change σ⁻¹ d.fst = d.snd ↔ σ d.snd = d.fst
    constructor
    · intro h
      simpa using (congrArg σ h).symm
    · intro h
      simpa using (congrArg (fun v => σ⁻¹ v) h).symm

private def shadow (σ : Perm V) : SimpleGraph V := SimpleGraph.fromRel (fun x y => σ x = y)

private theorem shadow_adj (hn : 3 ≤ Fintype.card V) (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) (x y : V) :
    (shadow σ).Adj x y ↔ σ x = y ∨ σ y = x := by
  rw [shadow, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    rintro rfl
    exact (no_short_cycle hn σ hσ x).1 (h.elim id id)

private theorem shadow_cycle (hn : 3 ≤ Fintype.card V) (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) :
    (shadow σ).Connected ∧ ∀ v, (shadow σ).degree v = 2 := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hstep (v : V) : (shadow σ).Adj v (σ v) :=
    (shadow_adj hn σ hσ _ _).mpr (Or.inl rfl)
  have hconn : (shadow σ).Connected := by
    letI : Nonempty V := hne
    apply Connected.mk
    intro a b
    obtain ⟨n,hnat⟩ := (hσ.2 (Set.mem_univ a) (Set.mem_univ b)).exists_nat_pow_eq
    have hi : Function.Semiconj (shadow σ).connectedComponentMk σ id := by
      intro v
      exact ConnectedComponent.sound (hstep v).reachable.symm
    have he := hi.iterate_right n a
    simp only [Perm.iterate_eq_pow, Function.iterate_id,id_eq,hnat] at he
    exact (ConnectedComponent.eq.mp he).symm
  refine ⟨hconn, fun v => ?_⟩
  have hdiff : σ v ≠ σ⁻¹ v := by
    intro h
    apply (no_short_cycle hn σ hσ v).2
    simpa using congrArg σ h
  have hset : (shadow σ).neighborSet v = {σ v,σ⁻¹ v} := by
    ext w
    rw [mem_neighborSet, shadow_adj hn σ hσ]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · right
        simpa using congrArg (fun v => σ⁻¹ v) h
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (by simp)
  have hcard : ((shadow σ).neighborSet v).ncard = 2 := by
    change σ v ≠ σ.symm v at hdiff
    rw [hset]
    simp [hdiff]
  simpa only [Set.ncard_eq_toFinset_card', ← (shadow σ).neighborFinset_def,
    (shadow σ).card_neighborFinset_eq_degree] using hcard

private structure Lift (F : SimpleGraph V) where
  E : V → V → Prop
  σ : Perm V
  edge : ∀ x y, E x y → F.Adj x y
  orient : ∀ x y, F.Adj x y → E x y ∨ E y x
  antisymm : ∀ x y, E x y → ¬ E y x
  outgoing : Relator.RightUnique E
  incoming : Relator.LeftUnique E
  full : σ.IsCycleOn Set.univ
  extension : ∀ x y, E x y → σ x = y

private def reverseLift {F : SimpleGraph V} (l : Lift F) : Lift F where
  E x y := l.E y x
  σ := l.σ⁻¹
  edge x y h := (l.edge y x h).symm
  orient x y h := (l.orient y x h.symm)
  antisymm x y h := l.antisymm y x h
  outgoing _ _ _ h h' := l.incoming h h'
  incoming _ _ _ h h' := l.outgoing h h'
  full := l.full.inv
  extension x y h := by
    have he := l.extension y x h
    simpa using (congrArg (fun v => l.σ⁻¹ v) he).symm

private theorem forced_orientation {F : SimpleGraph V} (hn : 3 ≤ Fintype.card V)
    (l : Lift F) (x y : V) : l.E x y ↔ F.Adj x y ∧ l.σ x = y := by
  constructor
  · exact fun h => ⟨l.edge _ _ h,l.extension _ _ h⟩
  · rintro ⟨hf,hs⟩
    rcases l.orient x y hf with h | h
    · exact h
    · have hr := l.extension _ _ h
      exact ((no_short_cycle hn l.σ l.full x).2 (by rw [hs,hr])).elim

private theorem lift_ext {F : SimpleGraph V} (hn : 3 ≤ Fintype.card V)
    {a b : Lift F} (h : a.σ = b.σ) : a = b := by
  have he : a.E = b.E := by
    funext x y
    apply propext
    rw [forced_orientation hn a, forced_orientation hn b,h]
  cases a
  cases b
  cases h
  cases he
  rfl

private def canonicalLift (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V)
    (σ : Perm V) (hf : σ.IsCycleOn Set.univ)
    (he : ∀ x y, F.Adj x y → σ x = y ∨ σ y = x) : Lift F where
  E x y := F.Adj x y ∧ σ x = y
  σ := σ
  edge _ _ h := h.1
  orient x y h := by
    rcases he x y h with hσ | hσ
    · exact Or.inl ⟨h,hσ⟩
    · exact Or.inr ⟨h.symm,hσ⟩
  antisymm x y h h' := (no_short_cycle hn σ hf x).2 (by rw [h.2,h'.2])
  outgoing _ _ _ h h' := h.2.symm.trans h'.2
  incoming _ _ _ h h' := σ.injective (h.2.trans h'.2.symm)
  full := hf
  extension _ _ h := h.2

private theorem reverse_involutive {F : SimpleGraph V} :
    Function.Involutive (@reverseLift V F) := by
  intro l
  cases l
  simp only [reverseLift,inv_inv]

private theorem reverse_distinct {F : SimpleGraph V} (hn : 3 ≤ Fintype.card V)
    (l : Lift F) : l ≠ reverseLift l := by
  intro h
  have he := congrArg Lift.σ h
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hne
  apply (no_short_cycle hn l.σ l.full v).2
  have he' := congrArg (fun σ : Perm V => σ v) he
  change l.σ v = l.σ⁻¹ v at he'
  simpa using congrArg l.σ he'

private def CompletedGraph (F : SimpleGraph V) :=
  {C : SimpleGraph V // C.Connected ∧ (∀ v, C.degree v = 2) ∧ F ≤ C}

private def forget (hn : 3 ≤ Fintype.card V) {F : SimpleGraph V}
    (l : Lift F) : CompletedGraph F :=
  ⟨shadow l.σ, (shadow_cycle hn l.σ l.full).1,
    (shadow_cycle hn l.σ l.full).2,
    fun x y h => (shadow_adj hn l.σ l.full x y).mpr
      ((l.orient x y h).elim (fun he => Or.inl (l.extension _ _ he))
        (fun he => Or.inr (l.extension _ _ he)))⟩

private theorem forget_reverse (hn : 3 ≤ Fintype.card V) {F : SimpleGraph V}
    (l : Lift F) : forget hn (reverseLift l) = forget hn l := by
  apply Subtype.ext
  ext x y
  rw [show (forget hn (reverseLift l)).val = shadow l.σ⁻¹ from rfl,
    show (forget hn l).val = shadow l.σ from rfl,
    shadow_adj hn _ l.full.inv, shadow_adj hn _ l.full]
  simp only [Perm.inv_eq_iff_eq]
  tauto

private theorem forget_surjective (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V) :
    Function.Surjective (forget hn (F := F)) := by
  intro C
  obtain ⟨σ,hσ,hgraph⟩ := raw_cycle_permutation C.val C.property.1 C.property.2.1
  let l := canonicalLift hn F σ hσ (fun x y h => (hgraph x y).mp (C.property.2.2 h))
  refine ⟨l,Subtype.ext ?_⟩
  ext x y
  exact (shadow_adj hn σ hσ x y).trans (hgraph x y).symm

private theorem forget_fiber (hn : 3 ≤ Fintype.card V) {F : SimpleGraph V}
    (a b : Lift F) : forget hn b = forget hn a ↔ b = a ∨ b = reverseLift a := by
  constructor
  · intro h
    have ha := shadow_cycle hn a.σ a.full
    have hb (x y : V) : (shadow a.σ).Adj x y ↔ b.σ x = y ∨ b.σ y = x := by
      have hh := congrArg Subtype.val h
      change shadow b.σ = shadow a.σ at hh
      rw [← hh]
      exact shadow_adj hn b.σ b.full x y
    rcases actual_permutation_fiber hn (shadow a.σ) ha.1 ha.2 a.σ b.σ a.full b.full
        (shadow_adj hn a.σ a.full) hb with h | h
    · exact Or.inl (lift_ext hn h)
    · exact Or.inr (lift_ext hn h)
  · rintro (rfl | rfl)
    · rfl
    · exact forget_reverse hn a

end D5.S3.Combinatorics.Graph.LinearForests.OrientationFibers
