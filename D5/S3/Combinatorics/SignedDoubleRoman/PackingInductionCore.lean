/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingInductionCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingInductionCore
   mirror-E: none(waiver:finite-carrier-induction)
   anchors: []
   utility: none
   digest: Residual induction selections lift with exact deletion and selection accounting. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtensionDegree

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore

open Finset MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restriction preserves the live support, degree bound, and forbidden clique. -/
theorem restriction_hypotheses (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S T : Finset V) (hT : T ⊆ S)
    (hdeg : DegreeBound C D S) (hno : C.CliqueFreeOn (S : Set V) 4) :
    let C' := (C.induce (T : Set V)).spanningCoe
    let D' := (D.induce (T : Set V)).spanningCoe
    letI := Classical.decRel C'.Adj
    letI := Classical.decRel D'.Adj
    Supported C' D' T ∧ DegreeBound C' D' T ∧ C'.CliqueFreeOn (T : Set V) 4 := by
  classical
  let C' := (C.induce (T : Set V)).spanningCoe
  let D' := (D.induce (T : Set V)).spanningCoe
  letI : DecidableRel C'.Adj := Classical.decRel _
  letI : DecidableRel D'.Adj := Classical.decRel _
  refine ⟨?_, ?_, ?_⟩
  · rintro u v (h | h)
    · obtain ⟨_, a, b, _, ha, hb⟩ := h
      exact ⟨ha ▸ a.property, hb ▸ b.property⟩
    · obtain ⟨_, a, b, _, ha, hb⟩ := h
      exact ⟨ha ▸ a.property, hb ▸ b.property⟩
  · intro v hv
    change (C'.neighborFinset v).card + (D'.neighborFinset v).card ≤ 3
    rw [restricted_neighbors C T v hv, restricted_neighbors D T v hv]
    exact (Nat.add_le_add (card_le_card inter_subset_left)
      (card_le_card inter_subset_left)).trans (hdeg v (hT hv))
  · intro K hK hKclique
    obtain ⟨hc, hk⟩ := C'.isNClique_iff.mp hKclique
    apply hno (hK.trans hT)
    refine (C.isNClique_iff).2 ⟨?_, hk⟩
    intro a ha b hb hab
    obtain ⟨_, x, y, hxy, hx, hy⟩ := hc ha hb hab
    exact hx ▸ hy ▸ hxy

/-- A selection gained in a deletion combines with any sufficiently large residual selection. -/
theorem lift_size (C D : SimpleGraph V) [DecidableRel D.Adj]
    (S R Q X : Finset V) (hR : R ⊆ S) (hQ : Q ⊆ R) (hX : X ⊆ S \ R)
    (hcount : R.card ≤ 3 * Q.card) (hsize : (S \ R).card ≤ 3 * X.card)
    (hgood : MixedAdmissible C D (X ∪ Q)) :
    ∃ Y : Finset V, Y ⊆ S ∧ MixedAdmissible C D Y ∧ S.card ≤ 3 * Y.card := by
  have hdisj : Disjoint X Q := by
    apply disjoint_left.mpr
    intro v hvX hvQ
    exact (mem_sdiff.mp (hX hvX)).2 (hQ hvQ)
  refine ⟨X ∪ Q, union_subset (hX.trans sdiff_subset) (hQ.trans hR), hgood, ?_⟩
  rw [card_union_of_disjoint hdisj]
  have hpartition := card_sdiff_add_card_eq_card hR
  omega

/-- A pair-constrained residual graph provides a smaller induction instance. -/
theorem reduce (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (S R Q : Finset V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hR : R ⊆ S) (hQ : Q ⊆ R) (hRne : R.Nonempty) (hcount : R.card ≤ 3 * Q.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hcolour : C.IsIndepSet (Q : Set V))
    (hboundary : ∀ q ∈ Q, ∀ t ∈ S \ R, ¬ C.Adj q t ∧ ¬ D.Adj q t)
    (hlocal : ∀ r ∈ R,
      ((insert r (D.neighborFinset r)) ∩ Q).card ≤ 2 ∧
      (((insert r (D.neighborFinset r)) ∩ Q).card = 2 →
        D.neighborFinset r ∩ (S \ R) = ∅) ∧
      (D.neighborFinset r ∩ (S \ R)).card ≤ 2)
    (hno : (ReducedColour C D R Q (S \ R)).CliqueFreeOn ((S \ R : Finset V) : Set V) 4) :
    ∃ Y : Finset V, Y ⊆ S ∧ MixedAdmissible C D Y ∧ S.card ≤ 3 * Y.card := by
  classical
  let T := S \ R
  let C' := ReducedColour C D R Q T
  let D' := (D.induce (T : Set V)).spanningCoe
  letI : DecidableRel C'.Adj := Classical.decRel _
  letI : DecidableRel D'.Adj := Classical.decRel _
  have hsmaller : T.card < S.card := by
    have hp := card_sdiff_add_card_eq_card hR
    have hn := card_pos.mpr hRne
    dsimp [T]
    omega
  have hs : Supported C' D' T := by
    rintro a b (h | h)
    · exact ⟨h.1, h.2.1⟩
    · obtain ⟨_, x, y, _, hx, hy⟩ := h
      exact ⟨hx ▸ x.property, hy ▸ y.property⟩
  obtain ⟨X, hX, hgood, hsize⟩ := ih T hsmaller C' D' hs
    (degree_preserved C D S R Q hdegree) hno
  exact lift_size C D S R Q X hR hQ hX hcount hsize
    (extend C D S R Q X hR hQ hsupport hX hcolour hboundary hlocal hgood)

/-- Clean deletions use ordinary induced relations without any newly imposed pair. -/
theorem clean_reduce (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (S R Q : Finset V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hR : R ⊆ S) (hQ : Q ⊆ R) (hRne : R.Nonempty) (hcount : R.card ≤ 3 * Q.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hcolour : C.IsIndepSet (Q : Set V))
    (hboundary : ∀ q ∈ Q, ∀ t ∈ S \ R, ¬ C.Adj q t ∧ ¬ D.Adj q t)
    (hlocal : ∀ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card +
      (D.neighborFinset r ∩ (S \ R)).card ≤ 2)
    (hno : C.CliqueFreeOn (S : Set V) 4) :
    ∃ Y : Finset V, Y ⊆ S ∧ MixedAdmissible C D Y ∧ S.card ≤ 3 * Y.card := by
  classical
  let T := S \ R
  let C' := (C.induce (T : Set V)).spanningCoe
  let D' := (D.induce (T : Set V)).spanningCoe
  letI : DecidableRel C'.Adj := Classical.decRel _
  letI : DecidableRel D'.Adj := Classical.decRel _
  have hsmaller : T.card < S.card := by
    have hp := card_sdiff_add_card_eq_card hR
    have hn := card_pos.mpr hRne
    dsimp [T]
    omega
  obtain ⟨hs, hd, hn⟩ := restriction_hypotheses C D S T sdiff_subset hdegree hno
  obtain ⟨X, hX, hgood, hsize⟩ := ih T hsmaller C' D' hs hd hn
  exact lift_size C D S R Q X hR hQ hX hcount hsize
    (extend_without_pairs C D S R Q X hR hQ hsupport hX hcolour hboundary hlocal hgood)

end D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore
