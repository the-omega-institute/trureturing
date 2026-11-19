import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerShapesProbe

/-! Counting distance-seven partners in one agreement direction. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)

attribute [local instance] Classical.propDecidable

open private directions mem_directions flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private antipode unusedDirections unused_card hamming_pair_antipode
  agreeing_coordinate_unused distanceSevenPartners distanceSeven_partner_card
  distanceSeven_partner_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe
open private distance_seven_agreement_count sum_cube_membership_property from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private eight_partner_adjacencies from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerShapesProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private lemma agreement_count_ge_degree {C : Finset (Q 9)} {x : Q 9}
    (u : unusedDirections C x) :
    (distanceSevenPartners C x).degree u ≤
      (C.filter fun y => hammingDist x y = 7 ∧ x u.val = y u.val).card := by
  classical
  let G := distanceSevenPartners C x
  rw [← G.card_neighborFinset_eq_degree]
  apply card_le_card_of_injOn
    (fun v => flip (flip (antipode x) u.val) v.val)
  · intro v hv
    have ha := (G.mem_neighborFinset u v).mp hv
    have hne : u.val ≠ v.val := fun h => ha.ne (Subtype.ext h)
    refine mem_filter.mpr ⟨ha.2, hamming_pair_antipode x hne, ?_⟩
    simp [BalancedCriticalSpectrum.flip, antipode, hne]
  · intro v _ w _ hvw
    exact Subtype.ext (flip_injective _ hvw)

/-- Agreement partners count at most four per unused direction. With eight
total partners every unused direction contributes at least two agreements. -/
theorem cube_lifted_agreement_capacity {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (x : Q 9) (i : Fin 9) :
    let n := ∑ y ∈ univ.filter (fun y => hammingDist x y = 7 ∧ x i = y i),
      cubePairMembership C x y
    let unused := cubeMembership C x - cubePairMembership C x (flip x i)
    n ≤ 4 * unused ∧
      ((C.filter (fun y => hammingDist x y = 7)).card = 8 → 2 * unused ≤ n) := by
  classical
  dsimp only
  by_cases hx : x ∈ C
  · have hs := sum_cube_membership_property C
      (fun y => hammingDist x y = 7 ∧ x i = y i)
    simp only [cubePairMembership, show cubeMembership C x = 1 by simp [cubeMembership, hx],
      one_mul, hs]
    by_cases hflip : flip x i ∈ C
    · have hzero : (C.filter (fun y => hammingDist x y = 7 ∧ x i = y i)) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro y hy hm
        have hn := agreeing_coordinate_unused hd hy hm.1 hm.2
        exact (mem_sdiff.mp hn).2 ((mem_directions C x i).mpr hflip)
      simp [cubeMembership, hflip, hzero]
    · simp only [cubeMembership, ite_eq_right hflip, sub_zero, mul_one]
      refine ⟨by exact_mod_cast (distance_seven_agreement_count hreg hb hd hx i).2, ?_⟩
      intro h8
      let u : unusedDirections C x := ⟨i, mem_sdiff.mpr
        ⟨mem_univ _, fun hm => hflip ((mem_directions C x i).mp hm)⟩⟩
      let G := distanceSevenPartners C x
      have hcard : Fintype.card (unusedDirections C x) = 6 := by simpa using unused_card hreg hx
      have hG : G.edgeFinset.card = 8 := (distanceSeven_partner_card hd x).trans h8
      obtain ⟨a, b, _, ha, hb', hother, _⟩ := eight_partner_adjacencies G hcard
        (distanceSeven_partner_degree hreg hb hd hx) hG
      have hdeg : 2 ≤ G.degree u := by
        by_cases hau : u = a
        · rw [hau, ha]
          decide
        by_cases hbu : u = b
        · rw [hbu, hb']
          decide
        · rw [hother u hau hbu]
      exact_mod_cast hdeg.trans (agreement_count_ge_degree u : _ ≤
        (C.filter fun y => hammingDist x y = 7 ∧ x i = y i).card)
  · simp [cubePairMembership, cubeMembership, hx]

#print axioms cube_lifted_agreement_capacity

end D5.S3.Combinatorics.Graph.HypercubeCritical
