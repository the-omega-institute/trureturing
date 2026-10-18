/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalTree
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalTree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unique tree paths identify precisely which independent bonds control three-terminal connectivity. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond

/-! Path edges, deleted-edge cuts and three-terminal independent bond laws. -/

set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree

open SimpleGraph
open scoped BigOperators
open ThreeTerminalBond

variable {V : Type*} {G : SimpleGraph V}

private lemma path_edges_subset_walk (hG : G.IsAcyclic) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (q : G.Walk u v) : p.edges ⊆ q.edges := by
  classical
  have heq : (⟨p,hp⟩ : G.Path u v) = q.toPath :=
    (hG.subsingleton_path u v).elim _ _
  have heq' : p = (q.toPath : G.Walk u v) := congrArg Subtype.val heq
  rw [heq']
  exact q.edges_toPath_subset_edges

private lemma path_mem_iff_cut (hG : G.IsAcyclic) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (e : Sym2 V) :
    e ∈ p.edges ↔ ¬ (G.deleteEdges {e}).Reachable u v := by
  classical
  constructor
  · intro he hr
    obtain ⟨q⟩ := hr
    have hmem : e ∈ (q.mapLe (G.deleteEdges_le {e})).edges :=
      path_edges_subset_walk hG p hp _ he
    rw [Walk.edges_mapLe_eq_edges] at hmem
    have := q.edges_subset_edgeSet hmem
    simpa using this
  · exact p.mem_edges_of_not_reachable_deleteEdges

private lemma not_mem_of_two_cuts {u v x y : V} (p : G.Walk u v) (hp : p.IsPath)
    (hu : ¬ (G.deleteEdges {s(x,y)}).Reachable u y)
    (hv : ¬ (G.deleteEdges {s(x,y)}).Reachable v y) : s(x,y) ∉ p.edges :=
  hp.isTrail.notMem_edges_of_not_reachable hu hv

private lemma no_three_path_edge (hG : G.IsAcyclic) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) (r : G.Walk a c)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (e : Sym2 V)
    (heP : e ∈ p.edges) (heQ : e ∈ q.edges) : e ∉ r.edges := by
  classical
  obtain ⟨x,y⟩ := e
  intro heR
  let H := G.deleteEdges {s(x,y)}
  have hab : ¬ H.Reachable a b := (path_mem_iff_cut hG p hp _).mp heP
  have hbc : ¬ H.Reachable b c := (path_mem_iff_cut hG q hq _).mp heQ
  by_cases ha : H.Reachable a y
  · have hb : ¬ H.Reachable b y := fun hb => hab (ha.trans hb.symm)
    have hc : ¬ H.Reachable c y := fun hc =>
      (path_mem_iff_cut hG r hr _).mp heR (ha.trans hc.symm)
    exact not_mem_of_two_cuts q hq hb hc heQ
  · have hb : H.Reachable b y := by
      by_contra hb
      exact not_mem_of_two_cuts p hp ha hb heP
    have hc : H.Reachable c y := by
      by_contra hc
      exact not_mem_of_two_cuts r hr ha hc heR
    exact hbc (hb.trans hc.symm)

/-- On an acyclic graph the third terminal path is the edge symmetric difference
of the first two. Empty paths and terminals in the middle remain included. -/
theorem path_edge_symmDiff (hG : G.IsAcyclic) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) (r : G.Walk a c)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (e : Sym2 V) :
    e ∈ r.edges ↔ (e ∈ p.edges ∧ e ∉ q.edges) ∨ (e ∈ q.edges ∧ e ∉ p.edges) := by
  classical
  have hRP : e ∈ r.edges → e ∈ p.edges ∨ e ∈ q.edges := by
    intro he
    have := path_edges_subset_walk hG r hr (p.append q) he
    simpa using this
  have hP : e ∈ p.edges → e ∈ r.edges ∨ e ∈ q.edges := by
    intro he
    have := path_edges_subset_walk hG p hp (r.append q.reverse) he
    simpa using this
  have hQ : e ∈ q.edges → e ∈ p.edges ∨ e ∈ r.edges := by
    intro he
    have := path_edges_subset_walk hG q hq (p.reverse.append r) he
    simpa using this
  have hno := no_three_path_edge hG p q r hp hq hr e
  tauto

noncomputable section

local instance classical_decidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- The open edges are a subset of the original graph's actual edge type. -/
def bondGraph (G : SimpleGraph V) (ω : G.edgeSet → Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ f : G.edgeSet, f.val = e ∧ ω f = true}

private lemma bondGraph_edges (ω : G.edgeSet → Bool) (e : G.edgeSet) :
    e.val ∈ (bondGraph G ω).edgeSet ↔ ω e = true := by
  classical
  simp only [bondGraph, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨f,hf,hω⟩,_⟩
    have : f = e := Subtype.ext hf
    simpa [this] using hω
  · intro hω
    exact ⟨⟨e,rfl,hω⟩, by simpa using G.not_isDiag_of_mem_edgeSet e.property⟩

private lemma bondGraph_le (ω : G.edgeSet → Bool) : bondGraph G ω ≤ G := by
  rw [← edgeSet_subset_edgeSet]
  intro e he
  simp only [bondGraph, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_setOf_eq] at he
  rcases he.1 with ⟨f,rfl,_⟩
  exact f.property

private lemma reachable_iff_path_open (hG : G.IsAcyclic) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (ω : G.edgeSet → Bool) :
    (bondGraph G ω).Reachable a b ↔
      ∀ e : G.edgeSet, e.val ∈ p.edges → ω e = true := by
  constructor
  · rintro ⟨q⟩ e he
    have hmem := path_edges_subset_walk hG p hp (q.mapLe (bondGraph_le ω)) he
    rw [Walk.edges_mapLe_eq_edges] at hmem
    exact (bondGraph_edges ω e).mp (q.edges_subset_edgeSet hmem)
  · intro h
    refine ⟨p.transfer (bondGraph G ω) ?_⟩
    intro e he
    exact (bondGraph_edges ω ⟨e,p.edges_subset_edgeSet he⟩).mpr
      (h ⟨e,p.edges_subset_edgeSet he⟩ he)

/-- A mode read from the actual open graph's path relation. -/
def graphMode (H : SimpleGraph V) (a b c : V) : Mode := by
  classical
  exact if H.Reachable a b then
    if H.Reachable b c then .all else .ab
  else if H.Reachable b c then .bc
  else if H.Reachable a c then .ac else .separate

/-- Finite independent-edge pushforward on the graph's edge subtype. -/
def bondLaw (G : SimpleGraph V) [Fintype G.edgeSet]
    (a b c : V) (θ : G.edgeSet → ℝ) (s : Mode) : ℝ := by
  classical
  exact ∑ ω : G.edgeSet → Bool,
    if graphMode (bondGraph G ω) a b c = s then weight θ ω else 0

private lemma cylinder_mass {E : Type*} [Fintype E] [DecidableEq E]
    (θ : E → ℝ) (S : Finset E) :
    (∑ ω : E → Bool, if (∀ e ∈ S, ω e = true) then weight θ ω else 0) =
      ∏ e ∈ S, θ e := by
  classical
  have hf (ω : E → Bool) :
      (if (∀ e ∈ S, ω e = true) then weight θ ω else 0) =
        ∏ e, if ω e then θ e else if e ∈ S then 0 else 1-θ e := by
    split_ifs with h
    · unfold weight
      apply Finset.prod_congr rfl
      intro e _
      cases he : ω e
      · have hn : e ∉ S := fun heS => by simpa [he] using h e heS
        simp [he,hn]
      · simp
    · push_neg at h
      obtain ⟨e,he,hω⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [he, Bool.eq_false_iff.mpr hω]
  simp_rw [hf]
  rw [← Fintype.prod_sum (fun (e : E) (x : Bool) =>
    if x then θ e else if e ∈ S then 0 else 1-θ e)]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  have hpoint (e : E) : θ e + (if e ∈ S then 0 else 1-θ e) =
      if e ∈ S then θ e else 1 := by split_ifs <;> ring
  simp_rw [hpoint]
  exact Finset.prod_ite_mem_eq S θ

private lemma bondLaw_sum [Fintype G.edgeSet] (a b c : V) (θ : G.edgeSet → ℝ) :
    ∑ s, bondLaw G a b c θ s = 1 := by
  classical
  unfold bondLaw
  rw [Finset.sum_comm]
  simpa using weight_sum θ

private lemma bondLaw_marginals [Fintype G.edgeSet] (a b c : V)
    (θ : G.edgeSet → ℝ) :
    (bondLaw G a b c θ .ab + bondLaw G a b c θ .all =
      ∑ ω : G.edgeSet → Bool, if (bondGraph G ω).Reachable a b then weight θ ω else 0) ∧
    (bondLaw G a b c θ .bc + bondLaw G a b c θ .all =
      ∑ ω : G.edgeSet → Bool, if (bondGraph G ω).Reachable b c then weight θ ω else 0) ∧
    (bondLaw G a b c θ .ac + bondLaw G a b c θ .all =
      ∑ ω : G.edgeSet → Bool, if (bondGraph G ω).Reachable a c then weight θ ω else 0) ∧
    (bondLaw G a b c θ .all =
      ∑ ω : G.edgeSet → Bool,
        if (bondGraph G ω).Reachable a b ∧ (bondGraph G ω).Reachable b c
        then weight θ ω else 0) := by
  classical
  repeat' constructor
  all_goals
    simp only [bondLaw, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    have h1 : (bondGraph G ω).Reachable a b → (bondGraph G ω).Reachable b c →
        (bondGraph G ω).Reachable a c := fun h h' => h.trans h'
    have h2 : (bondGraph G ω).Reachable a b → (bondGraph G ω).Reachable a c →
        (bondGraph G ω).Reachable b c := fun h h' => h.symm.trans h'
    have h3 : (bondGraph G ω).Reachable b c → (bondGraph G ω).Reachable a c →
        (bondGraph G ω).Reachable a b := fun h h' => h'.trans h.symm
    by_cases hab : (bondGraph G ω).Reachable a b <;>
      by_cases hbc : (bondGraph G ω).Reachable b c <;>
      by_cases hac : (bondGraph G ω).Reachable a c <;> simp_all [graphMode]

/-- Actual edge indices lying on a path. -/
def pathSupport [Fintype G.edgeSet] {a b : V} (p : G.Walk a b) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e => e.val ∈ p.edges

private lemma path_cylinder [Fintype G.edgeSet] (hG : G.IsAcyclic) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (ω : G.edgeSet → Bool) :
    (bondGraph G ω).Reachable a b ↔ ∀ e ∈ pathSupport p, ω e = true := by
  classical
  simpa [pathSupport] using reachable_iff_path_open hG p hp ω

/-- The complete five-law of every finite-edge tree is a three-arm law. The
three rates are products on pairwise disjoint sets of actual graph edges. -/
theorem tree_law [Fintype G.edgeSet] (hG : G.IsTree) (a b c : V)
    (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    ∃ A B C : ℝ, A ∈ Set.Icc 0 1 ∧ B ∈ Set.Icc 0 1 ∧ C ∈ Set.Icc 0 1 ∧
      bondLaw G a b c θ = law starEnds 0 1 2 ![A,B,C] := by
  classical
  obtain ⟨p,hp,_⟩ := hG.existsUnique_path a b
  obtain ⟨q,hq,_⟩ := hG.existsUnique_path b c
  obtain ⟨r,hr,_⟩ := hG.existsUnique_path a c
  let P := pathSupport p
  let Q := pathSupport q
  let R := pathSupport r
  let A := ∏ e ∈ P \ Q, θ e
  let B := ∏ e ∈ P ∩ Q, θ e
  let C := ∏ e ∈ Q \ P, θ e
  have hpq : Disjoint (P \ Q) (P ∩ Q) := by
    apply Finset.disjoint_left.mpr
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hpC : Disjoint P (Q \ P) := by
    apply Finset.disjoint_left.mpr
    simp only [Finset.mem_sdiff]
    tauto
  have hAC : Disjoint (P \ Q) (Q \ P) := by
    apply Finset.disjoint_left.mpr
    simp only [Finset.mem_sdiff]
    tauto
  have hP : (∏ e ∈ P, θ e) = A*B := by
    rw [← Finset.prod_union hpq]
    congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hQ : (∏ e ∈ Q, θ e) = B*C := by
    have hd : Disjoint (P ∩ Q) (Q \ P) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [← Finset.prod_union hd]
    congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hPQ : (∏ e ∈ P ∪ Q, θ e) = A*B*C := by
    rw [← hP, ← Finset.prod_union hpC]
    congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hR : (∏ e ∈ R, θ e) = A*C := by
    rw [← Finset.prod_union hAC]
    congr 1
    ext e
    simpa [P,Q,R,pathSupport] using
      path_edge_symmDiff hG.isAcyclic p q r hp hq hr e.val
  have hAB (ω) := path_cylinder hG.isAcyclic p hp ω
  have hBC (ω) := path_cylinder hG.isAcyclic q hq ω
  have hAC' (ω) := path_cylinder hG.isAcyclic r hr ω
  obtain ⟨hX,hY,hZ,hK⟩ := bondLaw_marginals a b c θ
  simp_rw [hAB] at hX hK
  simp_rw [hBC] at hY hK
  simp_rw [hAC'] at hZ
  have hK' : bondLaw G a b c θ .all = ∏ e ∈ P ∪ Q, θ e := by
    rw [hK, ← cylinder_mass θ (P ∪ Q)]
    apply Finset.sum_congr rfl
    intro ω _
    change (if (∀ e ∈ P, ω e = true) ∧ (∀ e ∈ Q, ω e = true)
      then weight θ ω else 0) =
        (if ∀ e ∈ P ∪ Q, ω e = true then weight θ ω else 0)
    by_cases hh : ∀ e ∈ P ∪ Q, ω e = true
    · have hh' := Finset.forall_mem_union.mp hh
      simp only [if_pos hh, if_pos hh']
    · have hh' : ¬ ((∀ e ∈ P, ω e = true) ∧ (∀ e ∈ Q, ω e = true)) :=
        fun h => hh (Finset.forall_mem_union.mpr h)
      simp only [if_neg hh, if_neg hh']
  rw [cylinder_mass, hP] at hX
  rw [cylinder_mass, hQ] at hY
  rw [cylinder_mass, hR] at hZ
  rw [hPQ] at hK'
  have hnorm := bondLaw_sum a b c θ
  have henum : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
  rw [henum] at hnorm
  simp at hnorm
  have hprod (S : Finset G.edgeSet) : (∏ e ∈ S, θ e) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨Finset.prod_nonneg (fun e _ => (hθ e).1),
     Finset.prod_le_one₀ (fun e _ => (hθ e).1) (fun e _ => (hθ e).2)⟩
  refine ⟨A,B,C,hprod _,hprod _,hprod _,?_⟩
  rw [star_law]
  funext s
  cases s <;> dsimp <;> linarith

/-- The constant-one inequality for every finite-edge tree, including zero
probability boundaries and coincident terminals. -/
theorem tree_bound [Fintype G.edgeSet] (hG : G.IsTree) (a b c : V)
    (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    0 ≤ delta (bondLaw G a b c θ) ∧
      delta (bondLaw G a b c θ) ≤ bondLaw G a b c θ .ac := by
  obtain ⟨A,B,C,hA,hB,hC,hp⟩ := tree_law hG a b c θ hθ
  rw [hp]
  exact star_bound A B C hA hB hC

#print axioms path_edge_symmDiff
#print axioms tree_law
#print axioms tree_bound
#print axioms path_edge_symmDiff

end

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
