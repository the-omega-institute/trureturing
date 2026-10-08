/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingPairUniqueness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingPairUniqueness
   mirror-E: none(waiver:saturated-pair-uniqueness)
   anchors: []
   utility: none
   digest: Identical surviving pairs inside a saturated four-clique have the same centre. -/

import D5.S3.Combinatorics.SignedDoubleRoman.CliqueSaturation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingPairUniqueness

open Finset MixedDefs CliqueSaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A duplicated imposed pair would lose two edges at an endpoint while adding only one. -/
theorem saturated_pair_unique (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (R Q T K : Finset V)
    (hdegree : ∀ v ∈ T, C.degree v + D.degree v ≤ 3)
    (hK : K ⊆ T) (hcard : K.card = 4)
    (hclique : (ReducedColour C D R Q T).IsClique (K : Set V))
    (r s p q : V) (hrR : r ∈ R) (hsR : s ∈ R)
    (hp : p ∈ K) (hpq : p ≠ q)
    (hrP : D.neighborFinset r ∩ T = {p, q})
    (hsP : D.neighborFinset s ∩ T = {p, q}) : r = s := by
  classical
  let C' := ReducedColour C D R Q T
  have hrp : D.Adj r p := by
    apply (D.mem_neighborFinset _ _).mp
    have hm : p ∈ D.neighborFinset r ∩ T := by rw [hrP]; simp
    exact (mem_inter.mp hm).1
  have hsp : D.Adj s p := by
    apply (D.mem_neighborFinset _ _).mp
    have hm : p ∈ D.neighborFinset s ∩ T := by rw [hsP]; simp
    exact (mem_inter.mp hm).1
  have hsat := saturated_four_clique C D R Q T K hdegree hK hcard hclique p hp
  obtain ⟨f, hf, hconstraints⟩ := added_neighbor_injection C D R Q T p
  have hcards : Fintype.card ↥(C'.neighborFinset p \ C.neighborFinset p) =
      Fintype.card ↥(D.neighborFinset p ∩ R) := by
    rw [Fintype.card_coe, Fintype.card_coe]
    have heq : (C'.neighborFinset p \ C.neighborFinset p).card =
        (D.neighborFinset p).card := hsat.2.2.2
    exact heq.trans (congrArg card hsat.2.2.1)
  have hsurj := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcards⟩
  obtain ⟨a, ha⟩ := hsurj.2 ⟨r,
    mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hrp.symm, hrR⟩⟩
  obtain ⟨b, hb⟩ := hsurj.2 ⟨s,
    mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hsp.symm, hsR⟩⟩
  have hra : (f a : V) = r := congrArg Subtype.val ha
  have hsb : (f b : V) = s := congrArg Subtype.val hb
  have hA : ∀ (z : ↥(C'.neighborFinset p \ C.neighborFinset p)) (c : V),
      (f z : V) = c → D.neighborFinset c ∩ T = {p, q} → (z : V) = q := by
    intro z c hzc hcP
    have hzN := (mem_sdiff.mp z.property).1
    have hzadj := (C'.mem_neighborFinset _ _).mp hzN
    have hzT := hzadj.2.1
    have hcz := (hconstraints z).2.2
    rw [hzc] at hcz
    have hzP : (z : V) ∈ D.neighborFinset c ∩ T :=
      mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hcz, hzT⟩
    rw [hcP] at hzP
    simpa only [mem_insert, mem_singleton, hzadj.ne.symm, false_or] using hzP
  have hab : a = b := Subtype.ext ((hA a r hra hrP).trans (hA b s hsb hsP).symm)
  exact hra.symm.trans ((congrArg (fun z => (f z : V)) hab).trans hsb)

end D5.S3.Combinatorics.SignedDoubleRoman.PackingPairUniqueness
