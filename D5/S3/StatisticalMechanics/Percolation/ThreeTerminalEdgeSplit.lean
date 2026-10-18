/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalEdgeSplit
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalEdgeSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint actual graph edges split into independent coordinates without changing the full terminal law. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate

/-! Exact coordinate changes for the complete independent-edge source. -/

set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalGluing ThreeTerminalCactusGate
open scoped BigOperators

noncomputable section

private lemma reindex_source_law {V E F : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E ≃ F) (ends : F → V × V) (a b c : V) (θ : F → ℝ) :
    law (fun i => ends (e i)) a b c (fun i => θ (e i)) = law ends a b c θ := by
  classical
  have hg (ω : F → Bool) :
      openGraph (fun i => ends (e i)) (fun i => ω (e i)) = openGraph ends ω := by
    ext x y
    simp only [openGraph,SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne,h | h⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨hne,Or.inl ⟨e i,hi,he⟩⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨hne,Or.inr ⟨e i,hi,he⟩⟩
    · rintro ⟨hne,h | h⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨hne,Or.inl ⟨e.symm i,by simpa using hi,by simpa using he⟩⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨hne,Or.inr ⟨e.symm i,by simpa using hi,by simpa using he⟩⟩
  have hp (ω : F → Bool) :
      partition (fun i => ends (e i)) a b c (fun i => ω (e i)) =
        partition ends a b c ω := by
    have hc (x y : V) :
        connected (fun i => ends (e i)) (fun i => ω (e i)) x y =
          connected ends ω x y := by
      by_cases hh : (openGraph ends ω).Reachable x y <;>
        simp [connected,hg,hh]
    simp only [partition,hc]
  have hw (ω : F → Bool) :
      weight (fun i => θ (e i)) (fun i => ω (e i)) = weight θ ω := by
    exact e.prod_comp (fun i => if ω i then θ i else 1-θ i)
  funext s
  unfold law
  rw [← (Equiv.arrowCongr e.symm (Equiv.refl Bool)).sum_comp]
  change (∑ ω : F → Bool,
    if partition (fun i => ends (e i)) a b c (fun i => ω (e i)) = s
    then weight (fun i => θ (e i)) (fun i => ω (e i)) else 0) = _
  simp_rw [hp,hw]

private def splitEquiv {V : Type*} (H K : SimpleGraph V)
    (h : Disjoint H.edgeSet K.edgeSet) :
    H.edgeSet ⊕ K.edgeSet ≃ (H ⊔ K).edgeSet := by
  classical
  exact (Equiv.Set.union h).symm.trans
    (Equiv.subtypeEquivProp (edgeSet_sup H K).symm)

/-- An actual graph union with disjoint edge sets is the independent sum of
its two actual-edge sources. This preserves the complete five-partition law,
including rates zero and one and repeated terminal labels. -/
theorem edge_split_law {V : Type*} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V)
    [Fintype H.edgeSet] [DecidableEq H.edgeSet]
    [Fintype K.edgeSet] [DecidableEq K.edgeSet]
    [Fintype (H ⊔ K).edgeSet] [DecidableEq (H ⊔ K).edgeSet]
    (h : Disjoint H.edgeSet K.edgeSet) (a b c : V)
    (θ : (H ⊔ K).edgeSet → ℝ) :
    bondLaw (H ⊔ K) a b c θ =
      law (Sum.elim (actualEdgeEnds H) (actualEdgeEnds K)) a b c
        (Sum.elim
          (fun e : H.edgeSet => θ ⟨e.val,edgeSet_mono le_sup_left e.property⟩)
          (fun e : K.edgeSet => θ ⟨e.val,edgeSet_mono le_sup_right e.property⟩)) := by
  classical
  let e := splitEquiv H K h
  have hends : (fun i => actualEdgeEnds (H ⊔ K) (e i)) =
      Sum.elim (actualEdgeEnds H) (actualEdgeEnds K) := by
    funext i
    cases i <;> rfl
  have hrates : (fun i => θ (e i)) = Sum.elim
      (fun i : H.edgeSet => θ ⟨i.val,edgeSet_mono le_sup_left i.property⟩)
      (fun i : K.edgeSet => θ ⟨i.val,edgeSet_mono le_sup_right i.property⟩) := by
    funext i
    cases i <;> rfl
  have hh := reindex_source_law e (actualEdgeEnds (H ⊔ K)) a b c θ
  rw [hends,hrates,actual_edge_law] at hh
  exact hh.symm

private lemma same_unordered_source {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (e f : E → V × V)
    (h : ∀ i, s((e i).1,(e i).2) = s((f i).1,(f i).2))
    (a b c : V) (θ : E → ℝ) : law e a b c θ = law f a b c θ := by
  classical
  have hg (ω : E → Bool) : openGraph e ω = openGraph f ω := by
    ext x y
    simp only [openGraph,SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne,hxy | hxy⟩
      all_goals obtain ⟨i,hi,he⟩ := hxy
      all_goals have hh := h i
      all_goals rw [he] at hh
      all_goals rcases Sym2.eq_iff.mp hh with hh | hh
      · exact ⟨hne,Or.inl ⟨i,hi,(Prod.ext hh.1.symm hh.2.symm)⟩⟩
      · exact ⟨hne,Or.inr ⟨i,hi,(Prod.ext hh.2.symm hh.1.symm)⟩⟩
      · exact ⟨hne,Or.inr ⟨i,hi,(Prod.ext hh.1.symm hh.2.symm)⟩⟩
      · exact ⟨hne,Or.inl ⟨i,hi,(Prod.ext hh.2.symm hh.1.symm)⟩⟩
    · rintro ⟨hne,hxy | hxy⟩
      all_goals obtain ⟨i,hi,he⟩ := hxy
      all_goals have hh := (h i).symm
      all_goals rw [he] at hh
      all_goals rcases Sym2.eq_iff.mp hh with hh | hh
      · exact ⟨hne,Or.inl ⟨i,hi,(Prod.ext hh.1.symm hh.2.symm)⟩⟩
      · exact ⟨hne,Or.inr ⟨i,hi,(Prod.ext hh.2.symm hh.1.symm)⟩⟩
      · exact ⟨hne,Or.inr ⟨i,hi,(Prod.ext hh.1.symm hh.2.symm)⟩⟩
      · exact ⟨hne,Or.inl ⟨i,hi,(Prod.ext hh.2.symm hh.1.symm)⟩⟩
  have hp (ω : E → Bool) : partition e a b c ω = partition f a b c ω := by
    have hc (x y : V) : connected e ω x y = connected f ω x y := by
      by_cases hh : (openGraph f ω).Reachable x y <;>
        simp [connected,hg,hh]
    simp only [partition,hc]
  funext z
  simp only [law,hp]

private lemma subtype_source_law {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (A : Set V) [Fintype A] [DecidableEq A]
    (ends : E → A × A) (a b c : A) (θ : E → ℝ) :
    law (fun i => ((ends i).1.val,(ends i).2.val)) a.val b.val c.val θ =
      law ends a b c θ := by
  classical
  let r : V → A := fun v => if hv : v ∈ A then ⟨v,hv⟩ else a
  have hr (v : A) : r v.val = v := by simp [r,v.property]
  let lifted : E → V × V := fun i => ((ends i).1.val,(ends i).2.val)
  have hadj (ω : E → Bool) (u v : A) :
      (openGraph lifted ω).Adj u.val v.val ↔ (openGraph ends ω).Adj u v := by
    simp only [openGraph,SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne,h | h⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨fun huv => hne (congrArg Subtype.val huv),
          Or.inl ⟨i,hi,Prod.ext (Subtype.ext (congrArg Prod.fst he))
            (Subtype.ext (congrArg Prod.snd he))⟩⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨fun huv => hne (congrArg Subtype.val huv),
          Or.inr ⟨i,hi,Prod.ext (Subtype.ext (congrArg Prod.fst he))
            (Subtype.ext (congrArg Prod.snd he))⟩⟩
    · rintro ⟨hne,h | h⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨fun huv => hne (Subtype.ext huv),Or.inl ⟨i,hi,by simp [lifted,he]⟩⟩
      · obtain ⟨i,hi,he⟩ := h
        exact ⟨fun huv => hne (Subtype.ext huv),Or.inr ⟨i,hi,by simp [lifted,he]⟩⟩
  have hsupport (ω : E → Bool) {x y : V} (h : (openGraph lifted ω).Adj x y) :
      x ∈ A ∧ y ∈ A := by
    obtain ⟨hne,h | h⟩ := h
    all_goals obtain ⟨i,hi,he⟩ := h
    · have hx : (ends i).1.val = x := congrArg Prod.fst he
      have hy : (ends i).2.val = y := congrArg Prod.snd he
      exact ⟨hx ▸ (ends i).1.property,hy ▸ (ends i).2.property⟩
    · have hy : (ends i).1.val = y := congrArg Prod.fst he
      have hx : (ends i).2.val = x := congrArg Prod.snd he
      exact ⟨hx ▸ (ends i).2.property,hy ▸ (ends i).1.property⟩
  have hreach (ω : E → Bool) (u v : A) :
      (openGraph lifted ω).Reachable u.val v.val ↔ (openGraph ends ω).Reachable u v := by
    let f : openGraph ends ω →g openGraph lifted ω :=
      ⟨Subtype.val,fun {u v} h => (hadj ω u v).2 h⟩
    let g : openGraph lifted ω →g openGraph ends ω :=
      ⟨r,fun {x y} h => (hadj ω (r x) (r y)).1 (by
        obtain ⟨hx,hy⟩ := hsupport ω h
        simpa [r,hx,hy] using h)⟩
    constructor
    · intro h
      simpa [g,hr] using h.map g
    · exact Reachable.map f
  have hp (ω : E → Bool) : partition lifted a.val b.val c.val ω =
      partition ends a b c ω := by
    have hc (x y : A) : connected lifted ω x.val y.val = connected ends ω x y := by
      by_cases hh : (openGraph ends ω).Reachable x y
      · have hh' := (hreach ω x y).2 hh
        simp [connected,hh,hh']
      · have hh' : ¬ (openGraph lifted ω).Reachable x.val y.val :=
          fun h => hh ((hreach ω x y).1 h)
        simp [connected,hh,hh']
    simp only [partition,hc]
  funext z
  unfold law
  change (∑ ω, if partition lifted a.val b.val c.val ω = z then weight θ ω else 0) = _
  simp_rw [hp]

private def sideEmbedding {V : Type*} (G : SimpleGraph V) (A : Set V) :
    G.induce A ↪g sideGraph G A where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by intro u v; simp [sideGraph,u.property,v.property]

/-- The actual-edge correspondence between an induced graph and the same
edge family on the original vertex type. -/
def inducedEdgeEquiv {V : Type*} (G : SimpleGraph V) (A : Set V) :
    (G.induce A).edgeSet ≃ (sideGraph G A).edgeSet :=
  Equiv.ofBijective (sideEmbedding G A).mapEdgeSet ⟨
    (sideEmbedding G A).mapEdgeSet.injective,by
      rintro ⟨e,he⟩
      induction e using Sym2.inductionOn with
      | hf x y =>
        change G.Adj x y ∧ x ∈ A ∧ y ∈ A at he
        refine ⟨⟨s(⟨x,he.2.1⟩,⟨y,he.2.2⟩),he.1⟩,?_⟩
        apply Subtype.ext
        rfl⟩

/-- Restricting the vertex type to a side retains the full actual five-mode
source, under the bijection of actual edges and their independent rates. -/
theorem induced_source_law {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Set V) [Fintype A] [DecidableEq A]
    [Fintype (G.induce A).edgeSet] [DecidableEq (G.induce A).edgeSet]
    [Fintype (sideGraph G A).edgeSet] [DecidableEq (sideGraph G A).edgeSet]
    (a b c : A) (θ : (sideGraph G A).edgeSet → ℝ) :
    bondLaw (sideGraph G A) a.val b.val c.val θ =
      bondLaw (G.induce A) a b c (fun i => θ (inducedEdgeEquiv G A i)) := by
  classical
  let e := inducedEdgeEquiv G A
  let f := actualEdgeEnds (G.induce A)
  have he (i : (G.induce A).edgeSet) :
      s(((f i).1 : V),((f i).2 : V)) =
        s((actualEdgeEnds (sideGraph G A) (e i)).1,
          (actualEdgeEnds (sideGraph G A) (e i)).2) := by
    have hh := congrArg (Sym2.map (Subtype.val : A → V))
      (Sym2.mk_fst_out_snd_out i.val)
    change s(((f i).1 : V),((f i).2 : V)) = (e i).val at hh
    exact hh.trans (Sym2.mk_fst_out_snd_out (e i).val).symm
  have h1 := reindex_source_law e (actualEdgeEnds (sideGraph G A))
    a.val b.val c.val θ
  have h2 := same_unordered_source
    (fun i => ((f i).1.val,(f i).2.val))
    (fun i => actualEdgeEnds (sideGraph G A) (e i)) he
    a.val b.val c.val (fun i => θ (e i))
  have h3 := subtype_source_law A f a b c (fun i => θ (e i))
  rw [actual_edge_law] at h1 h3
  exact h1.symm.trans (h2.symm.trans h3)

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.edge_split_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_split_law

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit.induced_source_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms induced_source_law

end
end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit
