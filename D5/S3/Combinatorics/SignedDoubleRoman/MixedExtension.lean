/- GID: D5/S3/Combinatorics/SignedDoubleRoman/MixedExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/MixedExtension
   mirror-E: none(waiver:mixed-packing-reduction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Deleted-centre pair constraints and extension of residual admissible selections. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Retained colour edges together with pairs imposed by capacity-one deleted centres. -/
noncomputable def ReducedColour (C D : SimpleGraph V) [DecidableRel D.Adj]
    (R Q T : Finset V) : SimpleGraph V where
  Adj a b := a ∈ T ∧ b ∈ T ∧ (C.Adj a b ∨ (a ≠ b ∧
    ∃ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card = 1 ∧
      (D.neighborFinset r ∩ T).card = 2 ∧ D.Adj r a ∧ D.Adj r b))
  symm := ⟨by
    rintro a b ⟨ha, hb, h | ⟨hne, r, hr, hq, hp, hra, hrb⟩⟩
    · exact ⟨hb, ha, Or.inl h.symm⟩
    · exact ⟨hb, ha, Or.inr ⟨hne.symm, r, hr, hq, hp, hrb, hra⟩⟩⟩
  loopless := ⟨by
    intro a h
    rcases h.2.2 with h | h
    · exact C.irrefl h
    · exact h.1 rfl⟩

/-- Native induced graphs retain exactly the neighbours belonging to the live carrier. -/
theorem restricted_neighbors (D : SimpleGraph V) [DecidableRel D.Adj]
    (T : Finset V) (v : V) (hv : v ∈ T) :
    let D' := (D.induce (T : Set V)).spanningCoe
    letI := Classical.decRel D'.Adj
    D'.neighborFinset v = D.neighborFinset v ∩ T := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter]
  constructor
  · rintro ⟨_, a, b, hab, ha, hb⟩
    exact ⟨ha ▸ hb ▸ hab, hb ▸ b.property⟩
  · intro hw
    exact ⟨hw.1.ne, ⟨v, hv⟩, ⟨w, hw.2⟩, hw.1, rfl, rfl⟩

/-- A residual selection lifts when each deleted centre has its remaining capacity enforced. -/
theorem extend (C D : SimpleGraph V) [DecidableRel D.Adj]
    (S R Q X : Finset V) (hR : R ⊆ S) (hQ : Q ⊆ R)
    (hsupport : Supported C D S) (hX : X ⊆ S \ R)
    (hcolour : C.IsIndepSet (Q : Set V))
    (hboundary : ∀ q ∈ Q, ∀ t ∈ S \ R, ¬ C.Adj q t ∧ ¬ D.Adj q t)
    (hlocal : ∀ r ∈ R,
      ((insert r (D.neighborFinset r)) ∩ Q).card ≤ 2 ∧
      (((insert r (D.neighborFinset r)) ∩ Q).card = 2 →
        D.neighborFinset r ∩ (S \ R) = ∅) ∧
      (D.neighborFinset r ∩ (S \ R)).card ≤ 2)
    (hadmissible :
      let C' := ReducedColour C D R Q (S \ R)
      let D' := (D.induce ((S \ R : Finset V) : Set V)).spanningCoe
      letI := Classical.decRel D'.Adj
      MixedAdmissible C' D' X) : MixedAdmissible C D (X ∪ Q) := by
  classical
  let T := S \ R
  let C' := ReducedColour C D R Q T
  let D' := (D.induce (T : Set V)).spanningCoe
  letI : DecidableRel D'.Adj := Classical.decRel _
  have hxq : Disjoint X Q := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hq
    exact (Finset.mem_sdiff.mp (hX hv)).2 (hQ hq)
  obtain ⟨hcX, hdX⟩ := hadmissible
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff] at hcX hcolour ⊢
    intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · intro hedge
      exact hcX ha hb hab ⟨hX ha, hX hb, Or.inl hedge⟩
    · exact fun hedge => (hboundary b hb a (hX ha)).1 hedge.symm
    · exact (hboundary a ha b (hX hb)).1
    · exact hcolour ha hb hab
  · intro v
    have hsplit : ((insert v (D.neighborFinset v)) ∩ (X ∪ Q)).card =
        ((insert v (D.neighborFinset v)) ∩ X).card +
        ((insert v (D.neighborFinset v)) ∩ Q).card := by
      rw [Finset.inter_union_distrib_left,
        Finset.card_union_of_disjoint (hxq.mono Finset.inter_subset_right
          Finset.inter_subset_right)]
    rw [hsplit]
    by_cases hvR : v ∈ R
    · have hnoX : v ∉ X := fun hv => (Finset.mem_sdiff.mp (hX hv)).2 hvR
      have hcap := hlocal v hvR
      change _ ≤ 2 ∧ (_ → D.neighborFinset v ∩ T = ∅) ∧
        (D.neighborFinset v ∩ T).card ≤ 2 at hcap
      have hsurv : (insert v (D.neighborFinset v)) ∩ X =
          (D.neighborFinset v ∩ T) ∩ X := by
        ext w
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, hwX⟩
          · exact (hnoX hwX).elim
          · exact ⟨⟨hw, hX hwX⟩, hwX⟩
        · rintro ⟨⟨hw, _⟩, hwX⟩
          exact ⟨Or.inr hw, hwX⟩
      rw [hsurv]
      by_cases hq2 : ((insert v (D.neighborFinset v)) ∩ Q).card = 2
      · have hempty := hcap.2.1 hq2
        change D.neighborFinset v ∩ T = ∅ at hempty
        rw [hempty, Finset.empty_inter, Finset.card_empty, hq2]
      · by_cases hq0 : ((insert v (D.neighborFinset v)) ∩ Q).card = 0
        · have hle := Finset.card_le_card
            (Finset.inter_subset_left (s₁ := D.neighborFinset v ∩ T) (s₂ := X))
          omega
        · have hq1 : ((insert v (D.neighborFinset v)) ∩ Q).card = 1 := by omega
          have hle : ((D.neighborFinset v ∩ T) ∩ X).card ≤ 1 := by
            by_cases hp2 : (D.neighborFinset v ∩ T).card = 2
            · apply Finset.card_le_one.mpr
              intro a ha b hb
              obtain ⟨⟨haD, haT⟩, haX⟩ := Finset.mem_inter.mp ha |>.imp
                (fun h => Finset.mem_inter.mp h) id
              obtain ⟨⟨hbD, hbT⟩, hbX⟩ := Finset.mem_inter.mp hb |>.imp
                (fun h => Finset.mem_inter.mp h) id
              by_contra hab
              have edge : C'.Adj a b :=
                ⟨haT, hbT, Or.inr ⟨hab, v, hvR, hq1, hp2,
                  (D.mem_neighborFinset _ _).mp haD,
                  (D.mem_neighborFinset _ _).mp hbD⟩⟩
              exact ((SimpleGraph.isIndepSet_iff C').mp hcX haX hbX hab) edge
            · have hh := Finset.card_le_card
                (Finset.inter_subset_left (s₁ := D.neighborFinset v ∩ T) (s₂ := X))
              omega
          omega
    · have hzero : (insert v (D.neighborFinset v)) ∩ Q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        obtain ⟨hclosed, hqQ⟩ := Finset.mem_inter.mp hq
        rcases Finset.mem_insert.mp hclosed with rfl | hedge
        · exact hvR (hQ hqQ)
        · have hvS := (hsupport (Or.inr
            ((D.mem_neighborFinset _ _).mp hedge))).1
          exact (hboundary q hqQ v (Finset.mem_sdiff.mpr ⟨hvS, hvR⟩)).2
            ((D.mem_neighborFinset _ _).mp hedge).symm
      rw [hzero, Finset.card_empty, Nat.add_zero]
      by_cases hvS : v ∈ S
      · have hvT : v ∈ T := Finset.mem_sdiff.mpr ⟨hvS, hvR⟩
        have heq : (insert v (D.neighborFinset v)) ∩ X =
            (insert v (D'.neighborFinset v)) ∩ X := by
          rw [restricted_neighbors D T v hvT]
          ext w
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | h, hx⟩
            · exact ⟨Or.inl rfl, hx⟩
            · exact ⟨Or.inr ⟨h, hX hx⟩, hx⟩
          · aesop
        rw [heq]
        exact hdX v
      · have hempty : (insert v (D.neighborFinset v)) ∩ X = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨hw, hx⟩ := Finset.mem_inter.mp hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hvS (Finset.mem_sdiff.mp (hX hx)).1
          · exact hvS (hsupport (Or.inr ((D.mem_neighborFinset _ _).mp hw))).1
        rw [hempty]
        simp

/-- When deleted centres have capacity for all survivors, no colour pair is needed. -/
theorem extend_without_pairs (C D : SimpleGraph V) [DecidableRel D.Adj]
    (S R Q X : Finset V) (hR : R ⊆ S) (hQ : Q ⊆ R)
    (hsupport : Supported C D S) (hX : X ⊆ S \ R)
    (hcolour : C.IsIndepSet (Q : Set V))
    (hboundary : ∀ q ∈ Q, ∀ t ∈ S \ R, ¬ C.Adj q t ∧ ¬ D.Adj q t)
    (hlocal : ∀ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card +
      (D.neighborFinset r ∩ (S \ R)).card ≤ 2)
    (hadmissible :
      let C' := (C.induce ((S \ R : Finset V) : Set V)).spanningCoe
      let D' := (D.induce ((S \ R : Finset V) : Set V)).spanningCoe
      letI := Classical.decRel D'.Adj
      MixedAdmissible C' D' X) : MixedAdmissible C D (X ∪ Q) := by
  classical
  apply extend C D S R Q X hR hQ hsupport hX hcolour hboundary
  · intro r hr
    have h := hlocal r hr
    refine ⟨by omega, ?_, by omega⟩
    intro hq
    have hp : (D.neighborFinset r ∩ (S \ R)).card = 0 := by omega
    exact Finset.card_eq_zero.mp hp
  · obtain ⟨hc, hd⟩ := hadmissible
    refine ⟨?_, hd⟩
    rw [SimpleGraph.isIndepSet_iff] at hc ⊢
    intro a ha b hb hab hedge
    rcases hedge.2.2 with hold | ⟨_, r, hr, hq, hp, _⟩
    · exact hc ha hb hab ⟨hold.ne, ⟨a, hX ha⟩, ⟨b, hX hb⟩, hold, rfl, rfl⟩
    · have h := hlocal r hr
      omega

end D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs
