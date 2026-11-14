/- GID: D5/S3/Combinatorics/Graph/StarForming/TripleRings
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/TripleRings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Arbitrary finite triple-port module rings with actual SF and beta attainment. -/

import D5.S3.Combinatorics.Graph.StarForming.TripleWitnesses

/-! The T_r construction in CUBIC_TRIPLE_PORT_COMPENSATION at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. A permutation parameter includes every cyclic size, singleton
restoration and empty family. Connectivity requires a separate orbit condition;
none is silently added to the parameter equalities. -/

namespace D5.S3.Combinatorics.Graph.StarForming.TripleRings
open StarFormingDissociationRefutation
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 48) where
  Adj a b := (a.1=b.1 ∧ TripleModule.graph.Adj a.2 b.2) ∨
    (a.2=16 ∧ b.1=e a.1 ∧ b.2=17) ∨ (a.2=17 ∧ b.1=e.symm a.1 ∧ b.2=16)
  symm := ⟨by
    rintro ⟨i,v⟩ ⟨j,w⟩ (⟨he,h⟩ | ⟨hv,hj,hw⟩ | ⟨hv,hj,hw⟩)
    · exact Or.inl ⟨he.symm,TripleModule.graph.adj_symm h⟩
    · exact Or.inr (Or.inr ⟨hw,by
        change j=e i at hj
        rw [hj]
        simp,hv⟩)
    · exact Or.inr (Or.inl ⟨hw,by
        change j=e.symm i at hj
        rw [hj]
        simp,hv⟩)⟩
  loopless := ⟨by
    rintro ⟨i,v⟩ (⟨_,h⟩ | ⟨h,_,h'⟩ | ⟨h,_,h'⟩)
    · exact TripleModule.graph.irrefl h
    all_goals have : (16 : Fin 48)=17 := by first | exact h.symm.trans h' | exact h'.symm.trans h
              exact (by decide : (16 : Fin 48)≠17) this⟩

instance (e : Equiv.Perm I) : DecidableRel (graph e).Adj :=
  fun _ _ => inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)))

def neighbors (e : Equiv.Perm I) (v : I × Fin 48) : List (I × Fin 48) :=
  (TripleModule.neighbors v.2).map (fun w => (v.1,w)) ++
    (if v.2=16 then [(e v.1,17)] else if v.2=17 then [(e.symm v.1,16)] else [])

private theorem adjacency_neighbors (e : Equiv.Perm I) (v w : I × Fin 48) :
    (graph e).Adj v w ↔ w∈neighbors e v := by
  rcases v with ⟨i,v⟩
  rcases w with ⟨j,w⟩
  by_cases h0 : v=16 <;> by_cases h1 : v=17 <;>
    simp [graph,neighbors,TripleModule.graph,h0,h1,Prod.mk.injEq,and_comm,and_left_comm]

private theorem neighbor_properties (e : Equiv.Perm I) (v : I × Fin 48) :
    (neighbors e v).Nodup ∧ (neighbors e v).length=3 := by
  rcases v with ⟨i,v⟩
  by_cases h0 : v=16
  · subst v
    simp [neighbors,TripleModule.neighbors]
  by_cases h1 : v=17
  · subst v
    simp [neighbors,TripleModule.neighbors]
  have hi : Function.Injective (fun w : Fin 48 => (i,w)) :=
    fun _ _ h => congrArg Prod.snd h
  have hn := (TripleWitnesses.local_class.2.1 v).map hi
  have hl := TripleWitnesses.local_class.2.2 v
  simpa [neighbors,h0,h1,hl] using And.intro hn hl

/-- Symbolic neighborhood lists prove cubicity for every finite permutation. -/
theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3 := by
  classical
  intro v
  have he : Finset.univ.filter ((graph e).Adj v)=(neighbors e v).toFinset := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    exact adjacency_neighbors e v w
  change (Finset.univ.filter ((graph e).Adj v)).card=3
  rw [he,List.toFinset_card_of_nodup (neighbor_properties e v).1,(neighbor_properties e v).2]

/-- The written bipartition colors the actual inter-module edges as well. -/
theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => TripleWitnesses.color v.2) ?_⟩
  rintro ⟨i,v⟩ ⟨j,w⟩ (⟨_,h⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩)
  · exact TripleWitnesses.local_class.1 v w h
  · change TripleWitnesses.color 16 ≠ TripleWitnesses.color 17
    decide +kernel
  · change TripleWitnesses.color 17 ≠ TripleWitnesses.color 16
    decide +kernel

def slice (S : Finset (I × Fin 48)) (i : I) : Finset (Fin 48) :=
  Finset.univ.filter (fun v => (i,v)∈S)

private theorem slice_independent (e : Equiv.Perm I) (S : Finset (I × Fin 48))
    (hS : IsKIndependent (graph e) 2 S) (i : I) :
    IsKIndependent TripleModule.graph 2 (slice S i) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  exact congrArg Prod.snd ((SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hS
    (i,c) (Finset.mem_filter.mp hc).2 (i,a) (Finset.mem_filter.mp ha).2
    (i,b) (Finset.mem_filter.mp hb).2 (Or.inl ⟨rfl,hca⟩) (Or.inl ⟨rfl,hcb⟩))

/-- The independent local omission budgets sum without reused vertices or credits. -/
theorem beta_upper (e : Equiv.Perm I) : beta (graph e) 2≤26*Fintype.card I := by
  classical
  apply Finset.sup_le
  intro S hS
  have hd := (Finset.mem_filter.mp hS).2
  rw [TripleModule.card_fibers]
  calc
    ∑ i : I, (Finset.univ.filter (fun v => (i,v)∈S)).card≤∑ _i : I,26 := by
      apply Finset.sum_le_sum
      intro i _
      exact TripleModule.beta_cap (slice S i) (slice_independent e S hd i)
    _ = 26*Fintype.card I := by simp [Nat.mul_comm]

private theorem independent_edge (e : Equiv.Perm I) (a b : I × Fin 48)
    (ha : TripleWitnesses.independent a.2) (hb : TripleWitnesses.independent b.2)
    (h : (graph e).Adj a b) : a.1=b.1 ∧ TripleModule.graph.Adj a.2 b.2 := by
  rcases h with h | ⟨_,_,hw⟩ | ⟨hv,_,_⟩
  · exact h
  · exact (TripleWitnesses.interface_states.2.2.2.1 (hw ▸ hb)).elim
  · exact (TripleWitnesses.interface_states.2.2.2.1 (hv ▸ ha)).elim

/-- The source twenty-six-set in every module attains the global upper bound. -/
theorem beta_lower (e : Equiv.Perm I) : 26*Fintype.card I≤beta (graph e) 2 := by
  classical
  let S : Finset (I × Fin 48) := Finset.univ.filter (fun v => TripleWitnesses.independent v.2)
  have hs : IsKIndependent (graph e) 2 S := by
    apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    rintro ⟨i,v⟩ hv ⟨j,a⟩ ha ⟨k,b⟩ hb hva hvb
    have hv' := (Finset.mem_filter.mp hv).2
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    obtain ⟨hij,hva'⟩ := independent_edge e (i,v) (j,a) hv' ha' hva
    obtain ⟨hik,hvb'⟩ := independent_edge e (i,v) (k,b) hv' hb' hvb
    have he := TripleWitnesses.independent_certificates.1 v a b hv' ha' hb' hva' hvb'
    exact Prod.ext (hij.symm.trans hik) he
  have hc : S.card=26*Fintype.card I := by
    rw [TripleModule.card_fibers]
    simp [S,TripleWitnesses.independent_certificates.2,Nat.mul_comm]
  rw [← hc]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hs⟩)

private theorem fiber_minimal : Regular.Minimal
    (fun a b : I × Fin 48 => a.1=b.1 ∧ TripleModule.graph.Adj a.2 b.2)
    (fun v => TripleWitnesses.forming v.2) := by
  classical
  let S := TripleWitnesses.forming
  let R := TripleModule.graph.Adj
  have hm := TripleWitnesses.forming_certificates.1
  refine ⟨?_,?_⟩
  · rintro ⟨i,v⟩ hv
    rcases hm.1 v hv with ⟨a,b,ha,hb,hne,hva,hvb⟩ | ⟨c,l,hc,hl,hvc,hcl⟩
    · exact Or.inl ⟨(i,a),(i,b),ha,hb,fun he => hne (congrArg Prod.snd he),
        ⟨rfl,hva⟩,⟨rfl,hvb⟩⟩
    · exact Or.inr ⟨(i,c),(i,l),hc,hl,⟨rfl,hvc⟩,⟨rfl,hcl⟩⟩
  · intro T hsub ⟨⟨i,d⟩,hd,hnot⟩ hT
    apply hm.2 (fun v => T (i,v)) (fun v hv => hsub _ hv) ⟨d,hd,hnot⟩
    intro v hv
    rcases hT (i,v) hv with ⟨⟨j,a⟩,⟨k,b⟩,ha,hb,hne,hva,hvb⟩ |
      ⟨⟨j,c⟩,⟨k,l⟩,hc,hl,hvc,hcl⟩
    · obtain ⟨rfl,hva⟩ := hva
      obtain ⟨rfl,hvb⟩ := hvb
      exact Or.inl ⟨a,b,ha,hb,fun he => hne (Prod.ext rfl he),hva,hvb⟩
    · obtain ⟨rfl,hvc⟩ := hvc
      obtain ⟨rfl,hcl⟩ := hcl
      exact Or.inr ⟨c,l,hc,hl,hvc,hcl⟩

/-- Rewiring only the omitted interface vertices preserves the full forming
minimality predicate, and actual fibers count twenty-eight vertices per module. -/
theorem sf_lower (e : Equiv.Perm I) : 28*Fintype.card I≤SF (graph e) 2 := by
  classical
  let S : Finset (I × Fin 48) := Finset.univ.filter (fun v => TripleWitnesses.forming v.2)
  have hm : Regular.Minimal (graph e).Adj (fun v => TripleWitnesses.forming v.2) := by
    apply Cubic.minimal_rewiring_forward _ _ _ ?_ fiber_minimal
    intro a b hsel
    constructor
    · exact Or.inl
    · rintro (h | ⟨hv,_,hw⟩ | ⟨hv,_,hw⟩)
      · exact h
      · rcases hsel with ha | hb
        · exact (TripleWitnesses.interface_states.1 (hv ▸ ha)).elim
        · exact (TripleWitnesses.interface_states.2.1 (hw ▸ hb)).elim
      · rcases hsel with ha | hb
        · exact (TripleWitnesses.interface_states.2.1 (hv ▸ ha)).elim
        · exact (TripleWitnesses.interface_states.1 (hw ▸ hb)).elim
  have hi : IsMinimalStarForming (graph e) 2 S := by
    apply (regular_minimal_iff _ _).mp
    simpa [S] using hm
  have hc : S.card=28*Fintype.card I := by
    rw [TripleModule.card_fibers]
    simp [S,TripleWitnesses.forming_certificates.2,Nat.mul_comm]
  rw [← hc]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

/-- Exact actual parameters for every finite module permutation, including
zero modules and singleton restoration. No finite list of ring sizes is used. -/
theorem parameters (e : Equiv.Perm I) :
    Fintype.card (I × Fin 48)=48*Fintype.card I ∧
    beta (graph e) 2=26*Fintype.card I ∧ SF (graph e) 2=28*Fintype.card I ∧
    SF (graph e) 2-beta (graph e) 2=2*Fintype.card I := by
  have hb := le_antisymm (beta_upper e) (beta_lower e)
  have hl := sf_lower e
  have hu := RegularCompensation.sf_regular_bound (graph e) (bipartite e) 3 (regular e)
  simp only [Fintype.card_prod,Fintype.card_fin] at hu
  rw [hb] at hu
  refine ⟨by simp [Nat.mul_comm],hb,?_,?_⟩ <;> omega

end D5.S3.Combinatorics.Graph.StarForming.TripleRings
