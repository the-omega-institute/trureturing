/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactus
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalCactus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite connected simple cactus satisfies the sharp constant-two bound. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalEdgeSplit

/-! Edge-count induction transports the complete actual source through cactus gates. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus

universe u

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalGluing
open ThreeTerminalProduct ThreeTerminalAttachment ThreeTerminalCactusSharpness
open ThreeTerminalCactusGate ThreeTerminalEdgeSplit
open scoped BigOperators
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

local instance classical_decidable (P : Prop) : Decidable P := Classical.propDecidable P

private def Strong (p : Mode → ℝ) : Prop :=
  0 ≤ delta p ∧ delta p+p .all*p .ac ≤ 2*p .ac

private lemma tree_strong {V : Type*} {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : G.IsTree) (a b c : V) (θ : G.edgeSet → ℝ)
    (hθ : ∀ e, θ e ∈ Set.Icc 0 1) : Strong (bondLaw G a b c θ) := by
  classical
  obtain ⟨A,B,C,hA,hB,hC,hp⟩ := tree_law hG a b c θ hθ
  rw [hp]
  have hid : delta (law starEnds 0 1 2 ![A,B,C])+
      law starEnds 0 1 2 ![A,B,C] .all*law starEnds 0 1 2 ![A,B,C] .ac =
      B*law starEnds 0 1 2 ![A,B,C] .ac := by
    rw [star_law]
    dsimp [delta]
    ring
  constructor
  · exact (star_bound A B C hA hB hC).1
  · rw [hid]
    have hpar : ∀ e : Fin 3, ![A,B,C] e ∈ Set.Icc (0:ℝ) 1 := by
      intro e
      fin_cases e
      · exact hA
      · exact hB
      · exact hC
    have hZ := (law_probability starEnds (0 : Fin 4) 1 2 ![A,B,C] hpar).1 .ac
    exact mul_le_mul_of_nonneg_right (le_trans hB.2 (by norm_num)) hZ

private lemma law_graph_congr {V : Type*} {G H : SimpleGraph V}
    [Fintype G.edgeSet] [Fintype H.edgeSet] (heq : G = H)
    (a b c : V) (θ : G.edgeSet → ℝ) :
    bondLaw G a b c θ = bondLaw H a b c
      (fun e => θ ⟨e.val,by simpa only [heq] using e.property⟩) := by
  subst H
  funext s
  unfold bondLaw
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  split_ifs
  · unfold weight
    apply Finset.prod_congr (by ext; simp)
    intro e _
    rfl
  · rfl

private lemma full_actual {V : Type*} (G : SimpleGraph V) :
    openGraph (actualEdgeEnds G) (fun _ => true) = G := by
  rw [actual_edge_graph]
  simpa [bondGraph] using fromEdgeSet_edgeSet G

private lemma glued_main {V : Type*} [Fintype V] [DecidableEq V]
    (G H K : SimpleGraph V) (A B : Set V) (g : V)
    (hcover : G = H ⊔ K) (h : OneVertexUnion H K A B g)
    (hd : Disjoint H.edgeSet K.edgeSet) (hgA : g ∈ A) (hgB : g ∈ B)
    (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1)
    (hmain : ∀ (a b c : A), Strong (bondLaw H a.val b.val c.val
      (fun e => θ ⟨e.val,by rw [hcover]; exact edgeSet_mono le_sup_left e.property⟩)))
    (a b c : V)
    (hs : (a ∈ A ∧ b ∈ A ∧ c ∈ A) ∨ ∃ port, Supported port A B a b c) :
    Strong (bondLaw G a b c θ) := by
  classical
  let θH : H.edgeSet → ℝ := fun e =>
    θ ⟨e.val,by rw [hcover]; exact edgeSet_mono le_sup_left e.property⟩
  let θK : K.edgeSet → ℝ := fun e =>
    θ ⟨e.val,by rw [hcover]; exact edgeSet_mono le_sup_right e.property⟩
  have hlaw : bondLaw G a b c θ =
      law (Sum.elim (actualEdgeEnds H) (actualEdgeEnds K)) a b c (Sum.elim θH θK) := by
    rw [law_graph_congr hcover a b c θ,edge_split_law H K hd]
  have hspl : OneVertexUnion (openGraph (actualEdgeEnds H) (fun _ => true))
      (openGraph (actualEdgeEnds K) (fun _ => true)) A B g := by
    simpa only [full_actual] using h
  rw [hlaw]
  rcases hs with ⟨ha,hb,hc⟩ | ⟨port,hs⟩
  · rw [joined_network_ignored _ _ A B a b c g hspl ha hb hc hgB θH θK,
      actual_edge_law]
    exact hmain ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩
  · have hgate : (gateTerminals port a b c g).1 ∈ A ∧
        (gateTerminals port a b c g).2.1 ∈ A ∧
        (gateTerminals port a b c g).2.2 ∈ A := by
      cases port <;> simp_all [Supported,gateTerminals]
    have hm := hmain ⟨_,hgate.1⟩ ⟨_,hgate.2.1⟩ ⟨_,hgate.2.2⟩
    rw [← actual_edge_law] at hm
    exact joined_network_invariant _ _ A B a b c g hspl port hs θH θK
      (fun e => hθ _) (fun e => hθ _) 2 (by norm_num) hm.1 hm.2

private lemma split_cases {V : Type*} {A B : Set V} (hcover : ∀ x, x ∈ A ∨ x ∈ B)
    (a b c : V) :
    ((a ∈ A ∧ b ∈ A ∧ c ∈ A) ∨ ∃ port, Supported port A B a b c) ∨
    ((a ∈ B ∧ b ∈ B ∧ c ∈ B) ∨ ∃ port, Supported port B A a b c) := by
  classical
  obtain ha | ha := hcover a <;> obtain hb | hb := hcover b <;>
    obtain hc | hc := hcover c
  · exact Or.inl (Or.inl ⟨ha,hb,hc⟩)
  · exact Or.inl (Or.inr ⟨.c,ha,hb,hc⟩)
  · exact Or.inl (Or.inr ⟨.b,ha,hc,hb⟩)
  · exact Or.inr (Or.inr ⟨.a,hb,hc,ha⟩)
  · exact Or.inl (Or.inr ⟨.a,hb,hc,ha⟩)
  · exact Or.inr (Or.inr ⟨.b,ha,hc,hb⟩)
  · exact Or.inr (Or.inr ⟨.c,ha,hb,hc⟩)
  · exact Or.inr (Or.inl ⟨ha,hb,hc⟩)

private lemma side_le {V : Type*} (G : SimpleGraph V) (A : Set V) :
    sideGraph G A ≤ G := fun _ _ h => h.1

/-- The strengthened sharp bound on the actual independent-edge source of
every finite connected simple cactus. Repeated marked vertices are included. -/
theorem cactus_invariant {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (hcactus : IsCactus G)
    (a b c : V) (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    0 ≤ delta (bondLaw G a b c θ) ∧
      delta (bondLaw G a b c θ)+bondLaw G a b c θ .all*bondLaw G a b c θ .ac ≤
        2*bondLaw G a b c θ .ac ∧
      delta (bondLaw G a b c θ) ≤ 2*bondLaw G a b c θ .ac := by
  classical
  suffices hs : Strong (bondLaw G a b c θ) by
    have hp := law_probability (actualEdgeEnds G) a b c θ hθ
    rw [actual_edge_law] at hp
    exact ⟨hs.1,hs.2,le_trans
      (le_add_of_nonneg_right (mul_nonneg (hp.1 .all) (hp.1 .ac))) hs.2⟩
  suffices h : ∀ n, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W), Nat.card H.edgeSet = n → H.Connected → IsCactus H →
      ∀ (a b c : W) (θ : H.edgeSet → ℝ), (∀ e, θ e ∈ Set.Icc 0 1) →
      Strong (bondLaw H a b c θ) from
    h (Nat.card G.edgeSet) (W := V) G rfl hG hcactus a b c θ hθ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H hn hH hC a b c θ hθ
    by_cases ha : H.IsAcyclic
    · exact tree_strong ⟨hH,ha⟩ a b c θ hθ
    · obtain ⟨o,C,hCyc⟩ : ∃ o, ∃ C : H.Walk o o, C.IsCycle := by
        simpa only [IsAcyclic,not_forall,not_not] using ha
      by_cases hspan : ∀ x, x ∈ C.support
      · exact ThreeTerminalCycle.cycle_invariant C hCyc
          (cycle_spanning_edges hC C hCyc hspan) a b c
          (hspan a) (hspan b) (hspan c) θ hθ
      · obtain ⟨x,hx⟩ := not_forall.mp hspan
        obtain ⟨g,hgC,hgA,hcover,hsplit,hd,hconnA,hconnB,hca,hcb,
          _,_,_,_,hcardA,hcardB⟩ := cycle_component_strict_edges hH hC C hCyc x hx
        let A := {v | (H.deleteEdges C.edgeSet).Reachable x v}
        let B := Aᶜ ∪ {g}
        have hgB : g ∈ B := by simp [B]
        have hA (a b c : A) : Strong (bondLaw (sideGraph H A) a.val b.val c.val
            (fun e => θ ⟨e.val,edgeSet_mono (side_le H A) e.property⟩)) := by
          rw [induced_source_law H A]
          exact ih _ (by simpa only [hn] using hcardA) (H.induce A) rfl
            hconnA hca a b c _ (fun e => hθ _)
        have hB (a b c : B) : Strong (bondLaw (sideGraph H B) a.val b.val c.val
            (fun e => θ ⟨e.val,edgeSet_mono (side_le H B) e.property⟩)) := by
          rw [induced_source_law H B]
          exact ih _ (by simpa only [hn] using hcardB) (H.induce B) rfl
            hconnB hcb a b c _ (fun e => hθ _)
        have hv : ∀ v, v ∈ A ∨ v ∈ B := by intro v; simp only [B,Set.mem_union,
          Set.mem_compl_iff,Set.mem_singleton_iff]; tauto
        rcases split_cases hv a b c with hs | hs
        · exact glued_main H (sideGraph H A) (sideGraph H B) A B g hcover hsplit hd
            hgA hgB θ hθ hA a b c hs
        · have hsplit' : OneVertexUnion (sideGraph H B) (sideGraph H A) B A g :=
            ⟨hsplit.right_support,hsplit.left_support,
              fun {_} hb ha => hsplit.intersection ha hb⟩
          exact glued_main H (sideGraph H B) (sideGraph H A) B A g
            (hcover.trans (sup_comm _ _)) hsplit' hd.symm hgB hgA θ hθ hB a b c hs

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus.cactus_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cactus_invariant


end
end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactus
