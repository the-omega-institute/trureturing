/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalGluing
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A one-vertex union preserves all three terminal connection relations simultaneously. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree

/-! Pointwise partition replacement at a single shared gate. -/

set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing

open SimpleGraph ThreeTerminalBond ThreeTerminalTree

variable {V : Type*} {H K : SimpleGraph V} {A B : Set V} {g : V}

/-- Both edge families have their endpoints on their own side, and the two
vertex sets intersect only at the gate. Isolated vertices need not be covered. -/
structure OneVertexUnion (H K : SimpleGraph V) (A B : Set V) (g : V) : Prop where
  left_support : ∀ ⦃u v⦄, H.Adj u v → u ∈ A ∧ v ∈ A
  right_support : ∀ ⦃u v⦄, K.Adj u v → u ∈ B ∧ v ∈ B
  intersection : ∀ ⦃v⦄, v ∈ A → v ∈ B → v = g

noncomputable section

local instance classical_decidable (P : Prop) : Decidable P := Classical.propDecidable P

private lemma collapse_reachable (h : OneVertexUnion H K A B g)
    {u v : V} (huv : (H ⊔ K).Reachable u v) :
    H.Reachable (if u ∈ A then u else g) (if v ∈ A then v else g) := by
  classical
  obtain ⟨p⟩ := huv
  have hedge {x y : V} (hxy : (H ⊔ K).Adj x y) :
      H.Reachable (if x ∈ A then x else g) (if y ∈ A then y else g) := by
    change H.Adj x y ∨ K.Adj x y at hxy
    rcases hxy with hxy | hxy
    · obtain ⟨hx,hy⟩ := h.left_support hxy
      simpa [hx,hy] using hxy.reachable
    · obtain ⟨hx,hy⟩ := h.right_support hxy
      have hcx : (if x ∈ A then x else g) = g := by
        split_ifs with hxA
        · exact h.intersection hxA hx
        · rfl
      have hcy : (if y ∈ A then y else g) = g := by
        split_ifs with hyA
        · exact h.intersection hyA hy
        · rfl
      rw [hcx,hcy]
  induction p with
  | nil => exact Reachable.rfl
  | cons hxy p ih => exact (hedge hxy).trans ih

/-- In a one-vertex union, the internal terminal connection and both cross-side
connections are preserved together, including terminals equal to the gate. -/
theorem simultaneous_reachability (h : OneVertexUnion H K A B g)
    {a b c : V} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ B) :
    ((H ⊔ K).Reachable a b ↔ H.Reachable a b) ∧
    ((H ⊔ K).Reachable a c ↔ H.Reachable a g ∧ K.Reachable g c) ∧
    ((H ⊔ K).Reachable b c ↔ H.Reachable b g ∧ K.Reachable g c) := by
  classical
  have hswap : OneVertexUnion K H B A g :=
    ⟨h.right_support,h.left_support,fun {_} hvB hvA => h.intersection hvA hvB⟩
  have hcA : (if c ∈ A then c else g) = g := by
    split_ifs with hcA
    · exact h.intersection hcA hc
    · rfl
  have haB : (if a ∈ B then a else g) = g := by
    split_ifs with haB
    · exact h.intersection ha haB
    · rfl
  have hbB : (if b ∈ B then b else g) = g := by
    split_ifs with hbB
    · exact h.intersection hb hbB
    · rfl
  constructor
  · constructor
    · intro hr
      simpa [ha,hb] using collapse_reachable h hr
    · exact Reachable.mono le_sup_left
  constructor
  · constructor
    · intro hr
      constructor
      · simpa [ha,hcA] using collapse_reachable h hr
      · have hr' : (K ⊔ H).Reachable a c := by simpa [sup_comm] using hr
        simpa [haB,hc] using collapse_reachable hswap hr'
    · rintro ⟨hag,hgc⟩
      exact (hag.mono le_sup_left).trans (hgc.mono le_sup_right)
  · constructor
    · intro hr
      constructor
      · simpa [hb,hcA] using collapse_reachable h hr
      · have hr' : (K ⊔ H).Reachable b c := by simpa [sup_comm] using hr
        simpa [hbB,hc] using collapse_reachable hswap hr'
    · rintro ⟨hbg,hgc⟩
      exact (hbg.mono le_sup_left).trans (hgc.mono le_sup_right)

/-- The entire five-mode partition transforms by keeping the third label when
its gate is connected, and detaching it otherwise. This is an identity for
each graph realization, before independent-edge probabilities are assigned. -/
theorem graphMode_pendant (h : OneVertexUnion H K A B g)
    {a b c : V} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ B) :
    graphMode (H ⊔ K) a b c =
      if K.Reachable g c then graphMode H a b g else
        match graphMode H a b g with
        | .all | .ab => .ab
        | _ => .separate := by
  classical
  obtain ⟨hab,hac,hbc⟩ := simultaneous_reachability h ha hb hc
  by_cases hgc : K.Reachable g c
  · simp only [hgc,ite_true,graphMode,hab,hbc,hac,and_true]
  · simp only [hgc,ite_false,graphMode,hab,hbc,hac,and_false]
    by_cases hab' : H.Reachable a b <;> by_cases hbg : H.Reachable b g <;>
      by_cases hag : H.Reachable a g <;> simp [hab',hbg,hag]

/-- An orientation of each actual undirected edge, without adding coordinates
for nonedges or identifying any distinct actual-edge coordinates. -/
def actualEdgeEnds (G : SimpleGraph V) (e : G.edgeSet) : V × V := e.val.out

theorem actual_edge_graph (G : SimpleGraph V) (ω : G.edgeSet → Bool) :
    openGraph (actualEdgeEnds G) ω = bondGraph G ω := by
  ext x y
  simp only [openGraph,SimpleGraph.fromRel_adj,bondGraph,
    SimpleGraph.fromEdgeSet_adj,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hne,(⟨e,hω,he⟩ | ⟨e,hω,he⟩)⟩
    · refine ⟨⟨e,?_,hω⟩,hne⟩
      have hr := Sym2.mk_fst_out_snd_out e.val
      change s((actualEdgeEnds G e).1,(actualEdgeEnds G e).2) = e.val at hr
      rw [he] at hr
      exact hr.symm
    · refine ⟨⟨e,?_,hω⟩,hne⟩
      have hr := Sym2.mk_fst_out_snd_out e.val
      change s((actualEdgeEnds G e).1,(actualEdgeEnds G e).2) = e.val at hr
      rw [he,Sym2.eq_swap] at hr
      exact hr.symm
  · rintro ⟨⟨e,he,hω⟩,hne⟩
    have hr : s((actualEdgeEnds G e).1,(actualEdgeEnds G e).2) = s(x,y) :=
      (Sym2.mk_fst_out_snd_out e.val).trans he
    rcases Sym2.eq_iff.mp hr with h | h
    · exact ⟨hne,Or.inl ⟨e,hω,Prod.ext h.1 h.2⟩⟩
    · exact ⟨hne,Or.inr ⟨e,hω,Prod.ext h.1 h.2⟩⟩

/-- The endpoint-indexed source is exactly the original graph's actual-edge
bond law, on the same configuration cube and with the same edge rates. -/
theorem actual_edge_law (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    (a b c : V) (θ : G.edgeSet → ℝ) :
    law (actualEdgeEnds G) a b c θ = bondLaw G a b c θ := by
  funext s
  unfold law bondLaw
  refine Finset.sum_congr (by ext ω; simp only [Finset.mem_univ]) ?_
  intro ω _
  have hm : partition (actualEdgeEnds G) a b c ω =
      graphMode (bondGraph G ω) a b c := by
    by_cases hab : (bondGraph G ω).Reachable a b <;>
      by_cases hbc : (bondGraph G ω).Reachable b c <;>
      by_cases hac : (bondGraph G ω).Reachable a c <;>
      simp [partition,connected,graphMode,actual_edge_graph,hab,hbc,hac]
  rw [hm]

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.simultaneous_reachability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simultaneous_reachability

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.graphMode_pendant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graphMode_pendant

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing.actual_edge_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_edge_law

end
end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
