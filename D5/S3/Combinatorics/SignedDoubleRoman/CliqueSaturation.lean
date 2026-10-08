/- GID: D5/S3/Combinatorics/SignedDoubleRoman/CliqueSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/CliqueSaturation
   mirror-E: none(waiver:reduction-clique-boundary)
   anchors: []
   utility: none
   digest: Degree saturation identifies every old edge at a newly created colour four-clique. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtensionDegree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.CliqueSaturation

open Finset MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A residual colour four-clique uses every incident edge of each of its vertices. -/
theorem saturated_four_clique (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (R Q T K : Finset V)
    (hdegree : ∀ v ∈ T, C.degree v + D.degree v ≤ 3)
    (hK : K ⊆ T) (hcard : K.card = 4)
    (hclique : (ReducedColour C D R Q T).IsClique (K : Set V)) :
    let C' := ReducedColour C D R Q T
    letI := Classical.decRel C'.Adj
    ∀ v ∈ K,
      C'.neighborFinset v = K.erase v ∧
      C.neighborFinset v = C.neighborFinset v ∩ K ∧
      D.neighborFinset v = D.neighborFinset v ∩ R ∧
      (C'.neighborFinset v \ C.neighborFinset v).card = (D.neighborFinset v).card := by
    classical
  dsimp only
  let C' := ReducedColour C D R Q T
  change ∀ v ∈ K,
    C'.neighborFinset v = K.erase v ∧
    C.neighborFinset v = C.neighborFinset v ∩ K ∧
    D.neighborFinset v = D.neighborFinset v ∩ R ∧
    (C'.neighborFinset v \ C.neighborFinset v).card = (D.neighborFinset v).card
  intro v hv
  have hvT := hK hv
  have hold : C'.neighborFinset v ∩ C.neighborFinset v =
      C.neighborFinset v ∩ T := by
    ext w
    simp only [mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hedge, hold⟩
      exact ⟨hold, hedge.2.1⟩
    · rintro ⟨hedge, hw⟩
      exact ⟨⟨hvT, hw, Or.inl hedge⟩, hedge⟩
  have hcliquesub : K.erase v ⊆ C'.neighborFinset v := by
    intro w hw
    obtain ⟨hne, hw⟩ := mem_erase.mp hw
    exact (C'.mem_neighborFinset _ _).mpr (hclique hv hw hne.symm)
  have hcliquecard : (K.erase v).card = 3 := by
    rw [card_erase_of_mem hv, hcard]
  have hmin : 3 ≤ (C'.neighborFinset v).card := by
    simpa only [hcliquecard] using card_le_card hcliquesub
  have hsplit := (C'.neighborFinset v).card_sdiff_add_card_inter (C.neighborFinset v)
  rw [hold] at hsplit
  have hcharge := added_neighbor_charge C D R Q T v
  change (C'.neighborFinset v \ C.neighborFinset v).card ≤
    (D.neighborFinset v ∩ R).card at hcharge
  have hCcard := card_le_card
    (inter_subset_left (s₁ := C.neighborFinset v) (s₂ := T))
  have hDcard := card_le_card
    (inter_subset_left (s₁ := D.neighborFinset v) (s₂ := R))
  have htotal : (C.neighborFinset v).card + (D.neighborFinset v).card ≤ 3 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree v hvT
  have hnewcard : (C'.neighborFinset v).card = 3 := by omega
  have hCeq : C.neighborFinset v ∩ T = C.neighborFinset v :=
    eq_of_subset_of_card_le inter_subset_left (by omega)
  have hDeq : D.neighborFinset v ∩ R = D.neighborFinset v :=
    eq_of_subset_of_card_le inter_subset_left (by omega)
  have hnew : C'.neighborFinset v = K.erase v := by
    exact (eq_of_subset_of_card_le hcliquesub (by omega)).symm
  refine ⟨hnew, ?_, hDeq.symm, by omega⟩
  apply (inter_eq_left.mpr ?_).symm
  intro w hw
  have hwT : w ∈ T := (mem_inter.mp (hCeq.symm ▸ hw)).2
  have hwnew : w ∈ C'.neighborFinset v :=
    (C'.mem_neighborFinset _ _).mpr
      ⟨hvT, hwT, Or.inl ((C.mem_neighborFinset _ _).mp hw)⟩
  rw [hnew] at hwnew
  exact mem_of_mem_erase hwnew

/-- Every old domination attachment of a saturated clique is an imposing centre. -/
theorem saturated_imposing_centres (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (R Q T K : Finset V)
    (hdegree : ∀ v ∈ T, C.degree v + D.degree v ≤ 3)
    (hdisjoint : Disjoint T R) (hK : K ⊆ T) (hcard : K.card = 4)
    (hclique : (ReducedColour C D R Q T).IsClique (K : Set V)) :
    ∀ v ∈ K, ∀ r, D.Adj v r → r ∈ R ∧
      ((insert r (D.neighborFinset r)) ∩ Q).card = 1 ∧
      ∃ a ∈ K, v ≠ a ∧ D.neighborFinset r ∩ T = {v, a} ∧
        ¬ C.Adj v a ∧ ¬ D.Adj v a := by
  classical
  let C' := ReducedColour C D R Q T
  letI : DecidableRel C'.Adj := Classical.decRel _
  intro v hv r hvr
  obtain ⟨hnew, _, hD, hcount⟩ :=
    saturated_four_clique C D R Q T K hdegree hK hcard hclique v hv
  obtain ⟨f, hf, hconstraint⟩ := added_neighbor_injection C D R Q T v
  have hrR : r ∈ R := by
    have hrN := (D.mem_neighborFinset _ _).mpr hvr
    rw [hD] at hrN
    exact (mem_inter.mp hrN).2
  have hcards : Fintype.card ↥(C'.neighborFinset v \ C.neighborFinset v) =
      Fintype.card ↥(D.neighborFinset v ∩ R) := by
    simpa only [Fintype.card_coe, ← hD] using hcount
  have hsurj := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcards⟩
  obtain ⟨a, ha⟩ := hsurj.2 ⟨r, mem_inter.mpr
    ⟨(D.mem_neighborFinset _ _).mpr hvr, hrR⟩⟩
  have hfa : (f a : V) = r := congrArg Subtype.val ha
  have hconstraints := hconstraint a
  rw [hfa] at hconstraints
  have haN : (a : V) ∈ C'.neighborFinset v := (mem_sdiff.mp a.property).1
  have haold : ¬ C.Adj v (a : V) := fun h =>
    (mem_sdiff.mp a.property).2 ((C.mem_neighborFinset _ _).mpr h)
  have hav : v ≠ (a : V) := ((C'.mem_neighborFinset _ _).mp haN).ne
  have haK : (a : V) ∈ K := by
    have heq : C'.neighborFinset v = K.erase v := hnew
    have haErase : (a : V) ∈ K.erase v := heq ▸ haN
    exact mem_of_mem_erase haErase
  refine ⟨hrR, hconstraints.1, a, haK, hav, ?_, haold, ?_⟩
  · symm
    apply eq_of_subset_of_card_le
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw <;> subst w
      · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hvr.symm, hK hv⟩
      · exact mem_inter.mpr
          ⟨(D.mem_neighborFinset _ _).mpr hconstraints.2.2, hK haK⟩
    · rw [hconstraints.2.1, card_pair hav]
  · intro hva
    have haR : (a : V) ∈ R := by
      have haD := (D.mem_neighborFinset _ _).mpr hva
      rw [hD] at haD
      exact (mem_inter.mp haD).2
    exact disjoint_left.mp hdisjoint (hK haK) haR

end D5.S3.Combinatorics.SignedDoubleRoman.CliqueSaturation
