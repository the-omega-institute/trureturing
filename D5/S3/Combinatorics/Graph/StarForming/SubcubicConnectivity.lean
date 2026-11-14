/- GID: D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual local core paths and all-size shared-port two-connectivity. -/

import D5.S3.Combinatorics.Graph.StarForming.SubcubicIdentification
import D5.S3.Combinatorics.Graph.StarForming.FiberConnectivity
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The two-connectivity proof of J_r from SUBCUBIC_STAR_FORMING_GAPS,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
The local core path certificates and the arbitrary orbit argument concern
the actual graph, including shared ports. -/
namespace D5.S3.Combinatorics.Graph.StarForming.SubcubicConnectivity
open SubcubicIdentification

private def coreGraph : SimpleGraph (Fin 10) := Subcubic.graph.comap Subcubic.coreLabel
private instance : DecidableRel coreGraph.Adj := fun a b =>
  inferInstanceAs (Decidable (Subcubic.Adj (Subcubic.coreLabel a) (Subcubic.coreLabel b)))
private def localRoot (z : Fin 10) : Fin 10 := if z=0 then 1 else 0
private def parent : Fin 10 → Fin 10 → Fin 10 := ![![1,1,8,8,9,3,2,1,1,1],
    ![0,0,6,5,5,0,0,0,3,4],
    ![0,7,0,5,5,0,0,0,3,4],
    ![0,7,6,0,5,0,0,0,2,4],
    ![0,7,6,5,0,0,0,0,3,1],
    ![0,7,6,8,9,0,0,0,2,1],
    ![0,7,8,5,5,0,0,0,3,4],
    ![0,8,6,5,5,0,0,0,3,4],
    ![0,7,6,5,5,0,0,0,0,4],
    ![0,7,6,5,5,0,0,0,3,0]]
private def rank : Fin 10 → Fin 10 → ℕ := ![![0,0,2,2,2,3,3,1,1,1],
    ![0,0,2,2,2,1,1,1,3,3],
    ![0,2,0,2,2,1,1,1,3,3],
    ![0,2,2,0,2,1,1,1,3,3],
    ![0,2,2,2,0,1,1,1,3,3],
    ![0,2,2,4,4,0,1,1,3,3],
    ![0,2,4,2,2,1,0,1,3,3],
    ![0,4,2,2,2,1,1,0,3,3],
    ![0,2,2,2,2,1,1,1,0,3],
    ![0,2,2,2,2,1,1,1,3,0]]

private theorem parent_facts : ∀ z a : Fin 10, a≠z → parent z a≠z ∧
    (a=localRoot z ∨ coreGraph.Adj a (parent z a) ∧ rank z (parent z a)<rank z a) := by
  decide +kernel

private theorem localRoot_survives (z : Fin 10) : localRoot z≠z := by
  unfold localRoot
  split <;> simp_all [eq_comm]

private theorem core_delete_preconnected (z : Fin 10) :
    (coreGraph.induce {a | a≠z}).Preconnected := by
  let p : {a : Fin 10 // a≠z} → {a : Fin 10 // a≠z} :=
    fun a => ⟨parent z a,(parent_facts z a a.property).1⟩
  apply FiberConnectivity.preconnected_of_rank _ ⟨localRoot z,localRoot_survives z⟩ p
    (fun a => rank z a)
  intro a ha
  rcases (parent_facts z a a.property).2 with h | h
  · exact (ha (Subtype.ext h)).elim
  · exact h

private theorem core_preconnected : coreGraph.Preconnected := by
  intro a b
  have hz : ∀ a b : Fin 10, ∃ z : Fin 10, a≠z ∧ b≠z := by decide +kernel
  obtain ⟨z,ha,hb⟩ := hz a b
  let f : (coreGraph.induce {a | a≠z}) →g coreGraph := ⟨fun a => a.val,fun h => h⟩
  exact ((core_delete_preconnected z) ⟨a,ha⟩ ⟨b,hb⟩).map f

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem core_reachable (e : Equiv.Perm I) (z : I × Fin 11)
    (i : I) (a b : Fin 10) (ha : core i a≠z) (hb : core i b≠z) :
    ((graph e).induce {x | x≠z}).Reachable ⟨core i a,ha⟩ ⟨core i b,hb⟩ := by
  by_cases hi : i=z.1
  · by_cases hz : z.2.val<10
    · let t : Fin 10 := ⟨z.2.val,hz⟩
      have ha' : a≠t := fun h => ha (Prod.ext hi (by rw [h]; exact Fin.ext rfl))
      have hb' : b≠t := fun h => hb (Prod.ext hi (by rw [h]; exact Fin.ext rfl))
      let f : (coreGraph.induce {a | a≠t}) →g ((graph e).induce {x | x≠z}) :=
        ⟨fun a => ⟨core i a.val,fun h => a.property (Fin.ext (congrArg (fun x : I × Fin 11 => x.2.val) h))⟩,
          fun h => (SubcubicIdentification.core_edges e i _ _).mpr h⟩
      exact ((core_delete_preconnected t) ⟨a,ha'⟩ ⟨b,hb'⟩).map f
    · let f : coreGraph →g ((graph e).induce {x | x≠z}) :=
        ⟨fun a => ⟨core i a,fun h => hz (by
          have he := congrArg (fun x : I × Fin 11 => x.2.val) h
          change a.val=z.2.val at he
          exact he ▸ a.isLt)⟩,
          fun h => (SubcubicIdentification.core_edges e i _ _).mpr h⟩
      exact (core_preconnected a b).map f
  · let f : coreGraph →g ((graph e).induce {x | x≠z}) :=
      ⟨fun a => ⟨core i a,fun h => hi (congrArg Prod.fst h)⟩,
        fun h => (SubcubicIdentification.core_edges e i _ _).mpr h⟩
    exact (core_preconnected a b).map f

private def root (z : Fin 11) : Fin 10 := if z=0 then 1 else 0
private theorem root_survives : ∀ z : Fin 11, (root z).castSucc≠z := by decide +kernel

/-- Every vertex-deleted shared-port assembly is preconnected when its
index permutation has a single orbit. -/
theorem delete_preconnected (e : Equiv.Perm I)
    (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (z : I × Fin 11) :
    ((graph e).induce {x | x≠z}).Preconnected := by
  let G := (graph e).induce {x | x≠z}
  let r : {x : I × Fin 11 // x≠z} :=
    ⟨core z.1 (root z.2),fun h => root_survives z.2 (congrArg Prod.snd h)⟩
  have path (q : Equiv.Perm I)
      (hq : ∀ i j, ∃ n : ℕ, (q : I → I)^[n] i=j) (p t : Fin 10)
      (hbridge : ∀ i, i≠z.1 → ∃ (hp : core i p≠z) (ht : core (q i) t≠z),
        G.Reachable ⟨core i p,hp⟩ ⟨core (q i) t,ht⟩) :
      ∀ i (v : Fin 10) (hv : core i v≠z), G.Reachable ⟨core i v,hv⟩ r := by
    have hn : ∀ n : ℕ, ∀ i, (q : I → I)^[n] i=z.1 →
        ∀ (v : Fin 10) (hv : core i v≠z), G.Reachable ⟨core i v,hv⟩ r := by
      intro n
      induction n with
      | zero =>
        intro i hi v hv
        change i=z.1 at hi
        subst i
        exact core_reachable e z z.1 v (root z.2) hv r.property
      | succ n ih =>
        intro i hi v hv
        by_cases he : i=z.1
        · subst i
          exact core_reachable e z z.1 v (root z.2) hv r.property
        · obtain ⟨hp,ht,hb⟩ := hbridge i he
          exact (core_reachable e z i v p hv hp).trans (hb.trans (ih (q i) hi t ht))
    intro i v hv
    obtain ⟨n,hi⟩ := hq i z.1
    exact hn n i hi v hv
  have hr : ∀ i (v : Fin 10) (hv : core i v≠z), G.Reachable ⟨core i v,hv⟩ r := by
    by_cases hz : z.2=9 ∨ z.2=10
    · have hi : ∀ i j, ∃ n : ℕ, (e.symm : I → I)^[n] i=j := by
        intro i j
        obtain ⟨n,hn⟩ := horbit j i
        refine ⟨n,?_⟩
        rw [← hn]
        exact (Function.LeftInverse.iterate e.symm_apply_apply n) j
      apply path e.symm hi 9 2
      intro i hi'
      have hp : core i (9 : Fin 10)≠z := fun h => hi' (congrArg Prod.fst h)
      have ht : core (e.symm i) (2 : Fin 10)≠z := by
        intro h
        have hh := congrArg Prod.snd h
        rcases hz with hz | hz <;> rw [hz] at hh <;> norm_num [core] at hh
      have hm : port i≠z := fun h => hi' (congrArg Prod.fst h)
      refine ⟨hp,ht,?_⟩
      have h1 : G.Adj ⟨core i (9 : Fin 10),hp⟩ ⟨port i,hm⟩ := by
        change (graph e).Adj _ _
        simp [graph,neighbors,core,port]
      have h2 : G.Adj ⟨port i,hm⟩ ⟨core (e.symm i) (2 : Fin 10),ht⟩ := by
        change (graph e).Adj _ _
        simp [graph,neighbors,core,port]
      exact h1.reachable.trans h2.reachable
    · apply path e horbit 2 9
      intro i hi
      have hp : core i (2 : Fin 10)≠z := fun h => hi (congrArg Prod.fst h)
      have ht : core (e i) (9 : Fin 10)≠z := by
        intro h
        exact hz (Or.inl (congrArg Prod.snd h).symm)
      have hm : port (e i)≠z := by
        intro h
        exact hz (Or.inr (congrArg Prod.snd h).symm)
      refine ⟨hp,ht,?_⟩
      have h1 : G.Adj ⟨core i (2 : Fin 10),hp⟩ ⟨port (e i),hm⟩ := by
        change (graph e).Adj _ _
        simp [graph,neighbors,core,port]
      have h2 : G.Adj ⟨port (e i),hm⟩ ⟨core (e i) (9 : Fin 10),ht⟩ := by
        change (graph e).Adj _ _
        simp [graph,neighbors,core,port]
      exact h1.reachable.trans h2.reachable
  have hall : ∀ a : {x : I × Fin 11 // x≠z}, G.Reachable a r := by
    rintro ⟨⟨i,v⟩,ha⟩
    by_cases hv : v.val<10
    · exact hr i ⟨v.val,hv⟩ ha
    · have he : v=10 := by apply Fin.ext; have := v.isLt; omega
      subst v
      by_cases h9 : core i (9 : Fin 10)≠z
      · have h : G.Adj ⟨(i,10),ha⟩ ⟨core i (9 : Fin 10),h9⟩ := by
          change (graph e).Adj _ _
          simp [graph,neighbors,core]
        exact h.reachable.trans (hr i 9 h9)
      · have he := not_ne_iff.mp h9
        have h2 : core (e.symm i) (2 : Fin 10)≠z := by
          intro h
          have hh := (congrArg Prod.snd h).trans (congrArg Prod.snd he).symm
          norm_num [core] at hh
        have h : G.Adj ⟨(i,10),ha⟩ ⟨core (e.symm i) (2 : Fin 10),h2⟩ := by
          change (graph e).Adj _ _
          simp [graph,neighbors,core]
        exact h.reachable.trans (hr (e.symm i) 2 h2)
  intro a b
  exact (hall a).trans (hall b).symm

/-- Connectivity before deletion follows from the same actual paths. -/
theorem preconnected (e : Equiv.Perm I)
    (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Preconnected := by
  intro a b
  have hz : ∀ a b : Fin 11, ∃ t : Fin 11, a≠t ∧ b≠t := by decide +kernel
  obtain ⟨t,ha,hb⟩ := hz a.2 b.2
  let z := (a.1,t)
  let f : ((graph e).induce {x | x≠z}) →g graph e := ⟨fun x => x.val,fun h => h⟩
  exact ((delete_preconnected e horbit z)
    ⟨a,fun h => ha (congrArg Prod.snd h)⟩
    ⟨b,fun h => hb (congrArg Prod.snd h)⟩).map f

/-- Actual two-connectivity, with nonemptiness and minimum order explicit. -/
theorem two_connected [Nonempty I] (e : Equiv.Perm I)
    (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) :
    (graph e).Connected ∧
    (∀ z : I × Fin 11, ((graph e).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (I × Fin 11) := by
  refine ⟨⟨preconnected e horbit⟩,?_,?_⟩
  · intro z
    exact { preconnected := delete_preconnected e horbit z
            nonempty := ⟨⟨core z.1 (root z.2),
              fun h => root_survives z.2 (congrArg Prod.snd h)⟩⟩ }
  · have hi := Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega

/-- All positive cyclic sizes are included; the bipartite parameter theorem
separately requires even size. -/
theorem cyclic_two_connected (r : ℕ) (hr : 0<r) :
    (graph (finRotate r)).Connected ∧
    (∀ z : Fin r × Fin 11, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧
    3≤Fintype.card (Fin r × Fin 11) := by
  letI : NeZero r := ⟨hr.ne'⟩
  apply two_connected
  intro i j
  refine ⟨(j-i).val,?_⟩
  rw [← finCycle_eq_finRotate_iterate]
  simp

end D5.S3.Combinatorics.Graph.StarForming.SubcubicConnectivity
