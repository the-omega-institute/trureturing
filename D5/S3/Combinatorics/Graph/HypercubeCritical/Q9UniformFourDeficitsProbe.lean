import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9DiameterCertificateProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerShapesProbe

/-! Equal coordinate deficits can force an impossible distance-seven partner graph. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
attribute [local instance] Classical.propDecidable

open private directions regular_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private antipode unusedDirections unused_card hamming_pair_antipode distanceSevenPartners
  distanceSeven_partner_card distanceSeven_partner_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private distance_seven_agreement_excludes_minority from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerWeightsProbe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private eight_partner_adjacencies from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerShapesProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- A Huang-balanced cubic support on 66 vertices cannot have nine true halves
of cardinality 25. A vertex with at least four true coordinates needs eight
distance-seven partners, although its partner graph has an isolated vertex. -/
theorem no_uniform_four_deficit_profile {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i : Fin 9, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * 4 = 33) :
    False := by
  let weight (x : Q 9) := (univ.filter fun i => x i = true).card
  have hhalfNat (i : Fin 9) : (C.filter fun x => x i = true).card = 25 := by
    have h := hhalf i
    omega
  have hweight : (∑ x ∈ C, weight x) = 225 := by
    have hw (x : Q 9) : weight x = ∑ i : Fin 9, if x i then (1 : ℕ) else 0 := by
      simp only [weight, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rfl
    simp_rw [hw]
    rw [sum_comm]
    simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one, hhalfNat, card_univ, Fintype.card_fin]
    norm_num
  have hlarge : ∃ x ∈ C, 4 ≤ weight x := by
    by_contra! h
    have hle : (∑ x ∈ C, weight x) ≤ ∑ _x ∈ C, 3 := by
      exact sum_le_sum fun x hx => by have hs := h x hx; omega
    rw [hweight, sum_const, nsmul_eq_mul, hC] at hle
    omega
  obtain ⟨x, hx, hxw⟩ := hlarge
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb
  have hsum := coordinate_profile_weight_bound hC hreg hb (fun _ => true) (fun _ => 4) hhalf hx
  have hsum' : (∑ i : Fin 9, if x i then (4 : ℤ) else 0) = 4 * (weight x : ℤ) := by
    simp only [weight, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  change 2 * (∑ i : Fin 9, if x i then (4 : ℤ) else 0) + 12 ≤
    (∑ _i : Fin 9, (4 : ℤ)) + (shell C x 7).card at hsum
  rw [hsum'] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h8 : (shell C x 7).card = 8 := by
    have hcap := sixty_six_distance_seven_le_eight hC hreg hb hd hx
    omega
  have hn := regular_directions C hreg hx
  let B : Finset (Fin 9) := univ.filter (fun i => x i = true)
  have hchoose : (B \ directions C x).Nonempty := by
    by_contra h
    have hs : B ⊆ directions C x := by
      intro i hi
      by_contra hni
      exact h ⟨i, mem_sdiff.mpr ⟨hi, hni⟩⟩
    have hle := card_le_card hs
    change B.card ≤ _ at hle
    change 4 ≤ B.card at hxw
    omega
  obtain ⟨i, hi⟩ := hchoose
  have hbit : x i = true := (mem_filter.mp (mem_sdiff.mp hi).1).2
  let t : unusedDirections C x := ⟨i, mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hi).2⟩⟩
  let G := distanceSevenPartners C x
  have hz : G.degree t = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro h
    obtain ⟨j, hj⟩ := (G.degree_pos_iff_exists_adj t).mp h
    change t ≠ j ∧ flip (flip (antipode x) i) j.val ∈ C at hj
    have hij : i ≠ j.val := fun he => hj.1 (Subtype.ext he)
    let y := flip (flip (antipode x) i) j.val
    have hxy : hammingDist x y = 7 := hamming_pair_antipode x hij
    have hagree : x i = y i := by
      simp [y, BalancedCriticalSpectrum.flip, antipode, hij]
    have hlow := distance_seven_agreement_excludes_minority hC hreg hb hd
      (fun _ => true) (fun _ => 4) (fun _ => by norm_num) hhalf hx hj.2 hxy hagree hbit
    norm_num at hlow
  have hV : Fintype.card (unusedDirections C x) = 6 := by simpa using unused_card hreg hx
  have he : G.edgeFinset.card = 8 := (distanceSeven_partner_card hd x).trans h8
  obtain ⟨a, b, _, ha, hb', hother, _⟩ := eight_partner_adjacencies G hV
    (distanceSeven_partner_degree hreg hb hd hx) he
  by_cases hta : t = a
  · rw [hta, ha] at hz
    omega
  by_cases htb : t = b
  · rw [htb, hb'] at hz
    omega
  have ht := hother t hta htb
  omega

#print axioms no_uniform_four_deficit_profile

/-- The remaining profiles exclude the uniform deficit-four case. -/
def sixtySixProfilesAfterUniformFour : List (List ℤ) :=
  sixtySixProfilesAfterDiameterCertificates.filter
    (· != List.ofFn (fun _ : Fin 9 => (4 : ℤ)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Reduce all finite profile filters, including the uniform-four exclusion.
theorem sixtySixProfilesAfterUniformFour_length : sixtySixProfilesAfterUniformFour.length = 57 := by
  decide +kernel

/-- A 66-point Huang-balanced cubic support normalizes to one of 57 profiles. -/
theorem q9_sixty_six_mem_profiles_after_uniform_four {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterUniformFour := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_diameter_certificates hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterUniformFour, List.mem_filter]
  refine ⟨hprofile, bne_iff_ne.mpr ?_⟩
  intro he
  have hr := List.ofFn_inj.mp he
  subst r
  exact no_uniform_four_deficit_profile hS hregS hbS hhalf

#print axioms q9_sixty_six_mem_profiles_after_uniform_four

end D5.S3.Combinatorics.Graph.HypercubeCritical
