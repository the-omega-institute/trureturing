import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneTwoHighClosureProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerShapesProbe

/-! Restrictions on the agreement coordinates of a distance-seven pair. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)
attribute [local instance] Classical.propDecidable
open private diff from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private unusedDirections unused_card distanceSevenPartners distanceSeven_partner_card
  distanceSeven_partner_degree hamming_pair_antipode antipode from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe
open private eight_partner_adjacencies from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerShapesProbe

private def signedDeficit {n : ℕ} (b : Fin n → Bool) (r : Fin n → ℤ) (x : Q n)
    (i : Fin n) : ℤ :=
  if x i = b i then r i else -r i

private lemma paired_coordinate_weights {n : ℕ} (b : Fin n → Bool) (r : Fin n → ℤ)
    (x y : Q n) :
    (∑ i : Fin n, if x i = b i then r i else 0) +
        (∑ i : Fin n, if y i = b i then r i else 0) =
      (∑ i, r i) + ∑ i ∈ univ.filter (fun i => x i = y i), signedDeficit b r x i := by
  rw [sum_filter, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> cases hb : b i <;>
    simp [signedDeficit, hx, hy, hb] <;> omega

private lemma agreement_card_two {x y : Q 9} (hxy : hammingDist x y = 7) :
    (univ.filter (fun i : Fin 9 => x i = y i)).card = 2 := by
  classical
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin 9)))
    (fun i => x i = y i)
  change (univ.filter (fun i : Fin 9 => x i = y i)).card + (diff x y).card = _ at hsum
  change (diff x y).card = 7 at hxy
  rw [hxy, card_univ, Fintype.card_fin] at hsum
  omega

/-- When every coordinate half has size at least 23, a distance-seven pair
cannot agree on the smaller side of a coordinate whose deficit is at least two. -/
private lemma distance_seven_agreement_excludes_minority
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (b : Fin 9 → Bool) (r : Fin 9 → ℤ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 5)
    (hc : ∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33)
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ C) (hxy : hammingDist x y = 7)
    {i : Fin 9} (hi : x i = y i) (hminor : x i = b i) : r i ≤ 1 := by
  classical
  let A := univ.filter (fun i : Fin 9 => x i = y i)
  have hiA : i ∈ A := mem_filter.mpr ⟨mem_univ _, hi⟩
  have hA : A.card = 2 := agreement_card_two hxy
  have hE : (A.erase i).card = 1 := by rw [card_erase_of_mem hiA, hA]
  obtain ⟨j, hj⟩ := card_eq_one.mp hE
  have hjA : j ∈ A.erase i := by rw [hj]; simp
  have hij : i ≠ j := (mem_erase.mp hjA).1.symm
  have heq : A = {i, j} := by rw [← insert_erase hiA, hj]
  have hX := coordinate_profile_weight_bound hC hreg hb b r hc hx
  have hY := coordinate_profile_weight_bound hC hreg hb b r hc hy
  have hcapX : ((shell C x 7).card : ℤ) ≤ 8 := by
    exact_mod_cast sixty_six_distance_seven_le_eight hC hreg hb hd hx
  have hcapY : ((shell C y 7).card : ℤ) ≤ 8 := by
    exact_mod_cast sixty_six_distance_seven_le_eight hC hreg hb hd hy
  have hpair := paired_coordinate_weights b r x y
  change _ = (∑ k, r k) + ∑ k ∈ A, signedDeficit b r x k at hpair
  rw [heq, sum_pair hij] at hpair
  have hjlo : -5 ≤ signedDeficit b r x j := by
    unfold signedDeficit
    split <;> linarith [(hr j).1, (hr j).2]
  rw [show signedDeficit b r x i = r i from ite_eq_left hminor] at hpair
  omega

#print axioms distance_seven_agreement_excludes_minority

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- At a vertex with eight distance-seven partners, each smaller-half
coordinate of deficit at least two is a direction of an actual incident edge. -/
theorem eight_partners_force_minority_directions_used
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (b : Fin 9 → Bool) (r : Fin 9 → ℤ)
    (hc : ∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33)
    (hNonneg : ∀ i, 0 ≤ r i)
    {x : Q 9} (hx : x ∈ C) (h8 : (shell C x 7).card = 8)
    {i : Fin 9} (hi : x i = b i) (hr : 2 ≤ r i) :
    flip x i ∈ C := by
  classical
  have hrange (j : Fin 9) : 0 ≤ r j ∧ r j ≤ 5 := by
    have hhalf : (23 : ℤ) ≤ (C.filter (fun y => y j = b j)).card := by
      exact_mod_cast huang_balanced_cubic_sixty_six_half_ge_twenty_three hC hreg hb j (b j)
    exact ⟨hNonneg j, by linarith [hc j]⟩
  by_contra hn
  have hiUnused : i ∈ unusedDirections C x := by
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    exact fun h => hn ((mem_directions C x i).mp h)
  let G := distanceSevenPartners C x
  let u : unusedDirections C x := ⟨i, hiUnused⟩
  have hV : Fintype.card (unusedDirections C x) = 6 := by simpa using unused_card hreg hx
  have he : G.edgeFinset.card = 8 := (distanceSeven_partner_card hd x).trans h8
  obtain ⟨a, d, _, ha, hD, hregular, _⟩ :=
    eight_partner_adjacencies G hV (distanceSeven_partner_degree hreg hb hd hx) he
  have hpos : 0 < G.degree u := by
    by_cases h₁ : u = a
    · rw [h₁, ha]; decide
    by_cases h₂ : u = d
    · rw [h₂, hD]; decide
    rw [hregular u h₁ h₂]
    decide
  obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp hpos
  have huv' : i ≠ v.val := fun h => huv.ne (Subtype.ext h)
  let y := flip (flip (antipode x) i) v.val
  have hy : y ∈ C := huv.2
  have hxy : hammingDist x y = 7 := hamming_pair_antipode x huv'
  have hAgree : x i = y i := by
    simp [y, BalancedCriticalSpectrum.flip, antipode, huv']
  have hsmall := distance_seven_agreement_excludes_minority hC hreg hb hd b r hrange
    hc hx hy hxy hAgree hi
  omega

#print axioms eight_partners_force_minority_directions_used

end D5.S3.Combinatorics.Graph.HypercubeCritical
