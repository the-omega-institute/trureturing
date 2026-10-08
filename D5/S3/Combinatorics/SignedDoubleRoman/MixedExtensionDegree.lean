/- GID: D5/S3/Combinatorics/SignedDoubleRoman/MixedExtensionDegree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/MixedExtensionDegree
   mirror-E: none(waiver:mixed-packing-degree-charge)
   anchors: []
   utility: none
   digest: Added colour neighbours inject into deleted domination neighbours. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtension

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each genuinely new neighbour can be assigned a distinct deleted imposing centre. -/
theorem added_neighbor_injection (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (R Q T : Finset V) (v : V) :
    let C' := ReducedColour C D R Q T
    letI := Classical.decRel C'.Adj
    ∃ f : ↥(C'.neighborFinset v \ C.neighborFinset v) →
        ↥(D.neighborFinset v ∩ R),
      Function.Injective f ∧ ∀ a,
        ((insert (f a : V) (D.neighborFinset (f a : V))) ∩ Q).card = 1 ∧
        (D.neighborFinset (f a : V) ∩ T).card = 2 ∧ D.Adj (f a : V) (a : V) := by
  classical
  let C' := ReducedColour C D R Q T
  letI : DecidableRel C'.Adj := Classical.decRel _
  let A := C'.neighborFinset v \ C.neighborFinset v
  have hwitness : ∀ a : A, ∃ r ∈ R,
      ((insert r (D.neighborFinset r)) ∩ Q).card = 1 ∧
      (D.neighborFinset r ∩ T).card = 2 ∧ D.Adj r v ∧ D.Adj r (a : V) := by
    intro a
    obtain ⟨ha, haold⟩ := Finset.mem_sdiff.mp a.property
    have hadj := (C'.mem_neighborFinset v a).mp ha
    rcases hadj.2.2 with h | h
    · exact (haold ((C.mem_neighborFinset v a).mpr h)).elim
    · exact h.2
  choose r hr hq hp hrv hra using hwitness
  let f : A → ↥(D.neighborFinset v ∩ R) := fun a =>
    ⟨r a, Finset.mem_inter.mpr ⟨(D.mem_neighborFinset v _).mpr (hrv a).symm, hr a⟩⟩
  refine ⟨f, ?_, fun a => ⟨hq a, hp a, hra a⟩⟩
  intro a b hab
  have hrab : r a = r b := congrArg Subtype.val hab
  have hav : v ≠ (a : V) := by
    have ha := (C'.mem_neighborFinset v a).mp (Finset.mem_sdiff.mp a.property).1
    exact ha.ne
  have hbv : v ≠ (b : V) := by
    have hb := (C'.mem_neighborFinset v b).mp (Finset.mem_sdiff.mp b.property).1
    exact hb.ne
  have hpair : ({v, (a : V)} : Finset V) = D.neighborFinset (r a) ∩ T := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw
      · subst w
        exact Finset.mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr (hrv a),
          ((C'.mem_neighborFinset v a).mp (Finset.mem_sdiff.mp a.property).1).1⟩
      · subst w
        exact Finset.mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr (hra a),
          ((C'.mem_neighborFinset v a).mp (Finset.mem_sdiff.mp a.property).1).2.1⟩
    · rw [hp a]
      simp [hav]
  have hbmem : (b : V) ∈ D.neighborFinset (r a) ∩ T := by
    rw [hrab]
    exact Finset.mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr (hra b),
      ((C'.mem_neighborFinset v b).mp (Finset.mem_sdiff.mp b.property).1).2.1⟩
  rw [← hpair] at hbmem
  have heq : (b : V) = (a : V) := by simpa [hbv.symm] using hbmem
  exact Subtype.ext heq.symm

/-- The injection bounds additions by the number of lost domination edges. -/
theorem added_neighbor_charge (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (R Q T : Finset V) (v : V) :
    let C' := ReducedColour C D R Q T
    letI := Classical.decRel C'.Adj
    (C'.neighborFinset v \ C.neighborFinset v).card ≤
      (D.neighborFinset v ∩ R).card := by
  classical
  obtain ⟨f, hf, _⟩ := added_neighbor_injection C D R Q T v
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Pair additions consume lost domination edges, preserving the total degree bound. -/
theorem degree_preserved (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S R Q : Finset V)
    (hdegree : DegreeBound C D S) :
    let C' := ReducedColour C D R Q (S \ R)
    let D' := (D.induce ((S \ R : Finset V) : Set V)).spanningCoe
    letI := Classical.decRel C'.Adj
    letI := Classical.decRel D'.Adj
    DegreeBound C' D' (S \ R) := by
  classical
  let T := S \ R
  let C' := ReducedColour C D R Q T
  let D' := (D.induce (T : Set V)).spanningCoe
  letI : DecidableRel C'.Adj := Classical.decRel _
  letI : DecidableRel D'.Adj := Classical.decRel _
  change ∀ v ∈ T, C'.degree v + D'.degree v ≤ 3
  intro v hv
  have hsplit := Finset.card_inter_add_card_sdiff (C'.neighborFinset v)
    (C.neighborFinset v)
  have hcharge := added_neighbor_charge C D R Q T v
  have hold : (C'.neighborFinset v ∩ C.neighborFinset v).card ≤ C.degree v :=
    Finset.card_le_card Finset.inter_subset_right
  have hdis : Disjoint (D.neighborFinset v ∩ R) (D.neighborFinset v ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro w hwR hwT
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwT).2).2
      (Finset.mem_inter.mp hwR).2
  have hsum : (D.neighborFinset v ∩ R).card +
      (D.neighborFinset v ∩ T).card ≤ D.degree v := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left
      Finset.inter_subset_left)
  have hd : D'.degree v = (D.neighborFinset v ∩ T).card :=
    restricted_neighbors D T v hv ▸ rfl
  have hc : C'.degree v = (C'.neighborFinset v).card := rfl
  have h := hdegree v (Finset.mem_sdiff.mp hv).1
  change (C'.neighborFinset v ∩ C.neighborFinset v).card +
    (C'.neighborFinset v \ C.neighborFinset v).card = (C'.neighborFinset v).card
    at hsplit
  change (C'.neighborFinset v \ C.neighborFinset v).card ≤
    (D.neighborFinset v ∩ R).card at hcharge
  omega

end D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs
