/- GID: D5/S3/Combinatorics/Graph/Laman/History
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/History
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Chain]
   utility: none
   digest: Laman counts characterize finite legal Henneberg histories from K2. -/
import D5.S3.Combinatorics.Graph.Laman.Moves
import Mathlib.Data.List.Chain

/-! # Legal Henneberg histories on canonical finite graph states -/

namespace SimpleGraph.Henneberg

/-- A canonical state has an unrestricted finite vertex count. -/
structure State where
  n : ℕ
  graph : SimpleGraph (Fin n)

/-- The initial graph has two vertices and its unique possible edge. -/
def base : State := ⟨2, ⊤⟩

/-- Each step is isomorphic to the actual Option-vertex operation, with all legal guards. -/
def Legal (s t : State) : Prop :=
  (∃ a b : Fin s.n, a ≠ b ∧ Nonempty (typeI s.graph a b ≃g t.graph)) ∨
  (∃ a b c : Fin s.n, s.graph.Adj a b ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧
    Nonempty (typeII s.graph a b c ≃g t.graph))

/-- A finite list of legal moves, with the empty list giving the zero-move history. -/
def HasHistory {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ l : List State, (base :: l).IsChain Legal ∧
    Nonempty (G ≃g ((base :: l).getLast (List.cons_ne_nil _ _)).graph)

private def typeICongr {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (a b : V) : typeI G a b ≃g typeI H (f a) (f b) where
  toEquiv := Equiv.optionCongr f.toEquiv
  map_rel_iff' {u v} := by
    cases u <;> cases v <;>
      simp [typeI, Equiv.optionCongr, f.injective.eq_iff, f.map_adj_iff]

private def typeIICongr {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (a b c : V) : typeII G a b c ≃g typeII H (f a) (f b) (f c) where
  toEquiv := Equiv.optionCongr f.toEquiv
  map_rel_iff' {u v} := by
    cases u <;> cases v <;>
      simp [typeII, Equiv.optionCongr, f.injective.eq_iff, f.map_adj_iff]

private theorem legal_preserves {s t : State} (h : Legal s t)
    (hs : s.graph.IsLaman) : t.graph.IsLaman := by
  rcases h with ⟨a, b, hab, ⟨f⟩⟩ | ⟨a, b, c, he, _, hca, hcb, ⟨f⟩⟩
  · exact SimpleGraph.IsLaman.iso f (typeI_isLaman hs hab)
  · exact SimpleGraph.IsLaman.iso f (typeII_isLaman hs hca hcb he)

private theorem reachable_of_laman :
    ∀ (n : ℕ) {V : Type*} [Fintype V], Fintype.card V = n →
      ∀ {G : SimpleGraph V}, G.IsLaman →
        ∃ t : State, Relation.ReflTransGen Legal base t ∧ Nonempty (G ≃g t.graph) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hV G h
    classical
    by_cases hV3 : 3 ≤ Fintype.card V
    · obtain ⟨v, hbranch⟩ := IsLaman.exists_typeI_or_typeII_reverse h hV3
      have hcard_lt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hV]
        exact Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      rcases hbranch with
        ⟨_, a, b, hab, hN, hsmall⟩ |
        ⟨_, a, b, c, hab, hca, hcb, hN, hnab, hsmall⟩
      · obtain ⟨s, hs, ⟨f⟩⟩ := ih _ hcard_lt rfl hsmall
        let φ := isoTypeIOfTwoNeighbors a.property.symm b.property.symm hN
        let H := typeI s.graph (f a) (f b)
        let t : State := ⟨Fintype.card (Option (Fin s.n)), H.overFin rfl⟩
        let ψ : G ≃g t.graph := φ.trans ((typeICongr f a b).trans (H.overFinIso rfl))
        refine ⟨t, hs.tail (Or.inl ⟨f a, f b, f.injective.ne hab, ?_⟩), ⟨ψ⟩⟩
        exact ⟨H.overFinIso rfl⟩
      · obtain ⟨s, hs, ⟨f⟩⟩ := ih _ hcard_lt rfl hsmall
        let φ := isoTypeIIOfThreeNeighbors a.property.symm b.property.symm c.property.symm hN hnab
        let H := typeII s.graph (f a) (f b) (f c)
        let t : State := ⟨Fintype.card (Option (Fin s.n)), H.overFin rfl⟩
        let ψ : G ≃g t.graph := φ.trans ((typeIICongr f a b c).trans (H.overFinIso rfl))
        have he : s.graph.Adj (f a) (f b) := f.map_adj_iff.mpr
          (show (G.comap Subtype.val ⊔ fromEdgeSet {s(a,b)}).Adj a b from
            Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hab⟩))
        refine ⟨t, hs.tail (Or.inr ⟨f a, f b, f c, he, f.injective.ne hab,
          f.injective.ne hca, f.injective.ne hcb, ?_⟩), ⟨ψ⟩⟩
        exact ⟨H.overFinIso rfl⟩
    · have hE := h.edgeSet_ncard
      rw [Nat.card_eq_fintype_card] at hE
      have hcard2 : Fintype.card V = 2 := by omega
      refine ⟨base, .refl, ?_⟩
      change Nonempty (G ≃g (⊤ : SimpleGraph (Fin 2)))
      rw [h.eq_top_of_card_eq_two hcard2]
      exact ⟨Iso.completeGraph (Fintype.equivFinOfCardEq hcard2)⟩

/-- The additive Laman counts on every induced vertex set characterize finite legal histories.
The statement applies in every universe and includes the zero-move K2 case. -/
theorem laman_iff_history {V : Type*} [Finite V] (G : SimpleGraph V) :
    (G.edgeSet.ncard + 3 = 2 * Nat.card V ∧
      ∀ S : Set V, 2 ≤ S.ncard → (G.induce S).edgeSet.ncard + 3 ≤ 2 * S.ncard) ↔
    HasHistory G := by
  classical
  have : Fintype V := Fintype.ofFinite V
  constructor
  · rintro ⟨hcount, hsub⟩
    have hL : G.IsLaman := by
      refine ⟨?_, hcount⟩
      intro s hs
      have h2 : 2 ≤ (s : Set V).ncard := by rw [Set.ncard_coe_finset]; omega
      have hb := hsub (s : Set V) h2
      rwa [← ncard_edgesIn_eq_ncard_induce_edgeSet, Set.ncard_coe_finset] at hb
    obtain ⟨t, ht, ⟨f⟩⟩ := reachable_of_laman _ rfl hL
    obtain ⟨l, hl, he⟩ := List.exists_isChain_cons_of_relationReflTransGen ht
    refine ⟨l, hl, ?_⟩
    rw [he]
    exact ⟨f⟩
  · rintro ⟨l, hl, ⟨f⟩⟩
    have ht := List.relationReflTransGen_of_exists_isChain_cons l hl rfl
    have hsound : ∀ {t : State}, Relation.ReflTransGen Legal base t → t.graph.IsLaman := by
      intro t ht
      induction ht with
      | refl => exact top_fin_two_isLaman
      | tail _ step ih => exact legal_preserves step ih
    have hL := hsound ht
    have hG := SimpleGraph.IsLaman.iso f.symm hL
    refine ⟨hG.edgeSet_ncard, ?_⟩
    intro S hS
    have hs := hG.isSparse S.toFinset (by rw [← Set.ncard_eq_toFinset_card']; omega)
    simpa only [Set.coe_toFinset, ← Set.ncard_eq_toFinset_card',
      ncard_edgesIn_eq_ncard_induce_edgeSet] using hs

end SimpleGraph.Henneberg
