/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4ZeroCutArithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4ZeroCutArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Zero-cut occupation under the four K4 star half bounds at order 72. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance

/-! Arithmetic and a parity constraint for zero cuts in the normalized K4 projection. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4ZeroCutArithmetic

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q IsBalanced flip_flip directionEndpoints directionEdges
  direction_edge_count)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open Q9SignedProjection (join fiber signedRow q9_signed_row_split)
open Q9TenPatternIncidence (tenProjection vertexCode midpointCode endpoints midpoint_cut
  exterior_constraints)
open Q9K4CutBalance
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private horizontal_total star_count_eq_half total_occupation sum_stars local_pairing
  label_contributions star_moments pairing_identity label_values countIf horizontal_endpoint_sum
  cutPotential cutPotential_eq ternary exists_ternary pattern_parities even_mul_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private transpose_mulVec signed_row_blocks from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence
open private signedRow_pairing_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint

local notation "flip" => BalancedCriticalSpectrum.flip

open Classical in
private theorem twelve_edges {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (d : Fin 9) : directionEdges C d = 12 := by
  have h := direction_edge_count (d := 3) C hreg hb d
  omega

private theorem crossing_card (C : Finset (Q 9)) (d : Fin 9) (b : Bool) :
    ((C.filter fun x => x d = b).filter (fun x => flip x d ∈ C)).card =
      directionEdges C d := by
  rw [filter_filter]
  cases b
  · rfl
  · symm
    unfold directionEdges
    apply card_bij (fun x _ => flip x d)
    · intro x hx
      obtain ⟨hx, hd, hf⟩ := mem_filter.mp hx
      simp [hx, hd, hf]
    · intro x _ y _ hxy
      simpa using congrArg (fun z => flip z d) hxy
    · intro y hy
      obtain ⟨hy, hd, hf⟩ := mem_filter.mp hy
      exact ⟨flip y d, by simp [hy, hd, hf], by simp⟩

open Classical in
/-- In an order-72 Huang-balanced cubic support, every coordinate half has even cardinality. -/
theorem coordinate_half_even {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (d : Fin 9) (b : Bool) :
    Even (C.filter fun x => x d = b).card := by
  let S := C.filter fun x => x d = b
  have hcount : 3 * S.card =
      ∑ j : Fin 9, (S.filter fun x => flip x j ∈ C).card := by
    calc
      _ = ∑ x ∈ S, (directions C x).card := by
        rw [sum_const_nat (m := 3)
          (fun x hx => regular_directions C hreg (mem_filter.mp hx).1)]
        exact Nat.mul_comm _ _
      _ = _ := by
        simp only [directions, card_filter]
        rw [Finset.sum_comm]
  have hcross : (S.filter fun x => flip x d ∈ C).card = 12 :=
    (crossing_card C d b).trans (twelve_edges hsize hreg hb d)
  have hinternal (j : Fin 9) (hj : j ≠ d) :
      (S.filter fun x => flip x j ∈ C).card = 2 * directionEdges S j := by
    rw [← endpoint_card_twice]
    congr 1
    ext x
    have hbit : flip x j d = x d := Function.update_of_ne (Ne.symm hj) _ _
    simp only [directionEndpoints, mem_filter, S, hbit]
    tauto
  rw [← sum_erase_add _ _ (mem_univ d), hcross] at hcount
  rw [sum_congr rfl (fun j hj => hinternal j (ne_of_mem_erase hj)), ← mul_sum] at hcount
  apply even_iff_two_dvd.mpr
  change 2 ∣ S.card
  omega

/-- Total even occupation in suffix fibers whose midpoint cut is zero. -/
def zeroCutOccupation (z : Q 9 → ℤ) : ℤ :=
  ∑ y : Q 5, if oddCount z y = 0 then evenCount (fun i => evenLabel z i y) else 0

open Classical in
private theorem occupation_totals {C : Finset (Q 9)} {z : Q 9 → ℤ} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (ha : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y)
    (ht : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y)) :
    0 ≤ zeroCutOccupation z ∧
      (∑ y, evenCount (fun i => evenLabel z i y)) = 24 + zeroCutOccupation z ∧
      (∑ y, oddCount z y) = 48 - zeroCutOccupation z ∧
      (∑ i, ∑ y, starCount z i y) = 120 - zeroCutOccupation z := by
  let A (y : Q 5) := evenCount (fun i => evenLabel z i y)
  let A₀ (y : Q 5) := if oddCount z y = 0 then A y else 0
  have hn : 0 ≤ zeroCutOccupation z := by
    apply sum_nonneg
    intro y _
    split
    · exact sum_nonneg (fun i _ => by unfold occupied; split <;> omega)
    · exact le_rfl
  have htotal := total_occupation hP hu hz
  rw [hsize] at htotal
  norm_num at htotal
  have hstars : (∑ i, ∑ y, starCount z i y) = (∑ y, A y) + 2 * (∑ y, oddCount z y) := by
    rw [Finset.sum_comm]
    simp [sum_stars, A, sum_add_distrib, mul_sum]
  have hedges := horizontal_total hreg hP hu hz hrow ha
  simp only [twelve_edges hsize hreg hb, Nat.cast_ofNat, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, local_pairing (ht _)] at hedges
  have hsplit (y : Q 5) : (if oddCount z y = 0 then 0 else 2 * A y) =
      2 * A y - 2 * A₀ y := by
    by_cases h : oddCount z y = 0 <;> simp [A₀, h]
  change (∑ y, if oddCount z y = 0 then 0 else 2 * A y) = _ at hedges
  simp_rw [hsplit, sum_sub_distrib, ← mul_sum] at hedges
  change 2 * (∑ y, A y) - 2 * zeroCutOccupation z = 48 at hedges
  change (∑ y, A y) + (∑ y, oddCount z y) = 72 at htotal
  have hA : (∑ y, A y) = 24 + zeroCutOccupation z := by omega
  have hO : (∑ y, oddCount z y) = 48 - zeroCutOccupation z := by
    rw [hA] at htotal
    omega
  refine ⟨hn, hA, hO, ?_⟩
  rw [hstars, hA, hO]
  omega

private theorem half_pairing {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (hrows : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
      signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (ht : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hodd : (∑ y, oddCount z y) = 48 - zeroCutOccupation z) (i : Fin 4) :
    6 * (3 * activeCenters z i + activePartners z i + 2 * activeBalanced z i) =
      4 * (∑ y, starCount z i y) - 48 + zeroCutOccupation z := by
  have hstar := sum_congr (s₁ := (univ : Finset (Q 5))) rfl
    (fun y _ => (star_moments hP hu hz hrow i y).2)
  simp only [sum_sub_distrib, ← mul_sum, hodd] at hstar
  change 4 * ((∑ y, starCount z i y) - labelCount z i) -
    (∑ y, cScaled z i y ^ 2) = 48 - zeroCutOccupation z at hstar
  have hp := pairing_identity (evenLabel z i) (cScaled z i)
    (fun y => (hrows i y).1) (fun y => (hrows i y).2)
  have hsq (y : Q 5) : evenLabel z i y ^ 2 = occupied (evenLabel z i y) := by
    rcases label_values hu hz (join (pattern (vertexCode i)) y) with h | h | h <;>
      change evenLabel z i y = _ at h <;> norm_num [h, occupied]
  simp only [hsq] at hp
  change 6 * (∑ y, evenLabel z i y * cScaled z i y) =
    4 * labelCount z i + ∑ y, cScaled z i y ^ 2 at hp
  have hpair : (∑ y, evenLabel z i y * cScaled z i y) =
      3 * activeCenters z i + activePartners z i + 2 * activeBalanced z i := by
    unfold activeCenters activePartners activeBalanced
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun y _ => ?_)
    by_cases ho : oddCount z y = 0
    · rcases ht y with ⟨hc, _, _⟩ | ⟨j, sign, h, _, _⟩ | ⟨h, _, _, _⟩
      · simp [ho, show cScaled z i y = 0 from hc i, countIf]
      · omega
      · omega
    · exact (label_contributions (i := i) (ht y) (fun h => (ho h).elim)).2.2
  omega

private theorem half_cases (H : Fin 4 → ℤ) (Z : ℤ)
    (hn : 0 ≤ Z) (hs : (∑ i, H i) = 120 - Z)
    (hl : ∀ i, 28 ≤ H i) (he : ∀ i, 2 ∣ H i)
    (hm : ∀ i, 6 ∣ 4 * H i - 48 + Z) :
    (Z = 0 ∧ ∀ i, H i = 30) ∨ Z = 2 ∨ (Z = 8 ∧ ∀ i, H i = 28) := by
  have hl0 := hl 0
  have hl1 := hl 1
  have hl2 := hl 2
  have hl3 := hl 3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero] at hs
  have hZ : Z ≤ 8 := by omega
  have hZcases : Z = 0 ∨ Z = 2 ∨ Z = 8 := by
    have hm0 := hm 0
    have hm1 := hm 1
    have hm2 := hm 2
    have hm3 := hm 3
    have he0 := he 0
    have he1 := he 1
    have he2 := he 2
    have he3 := he 3
    interval_cases Z <;> norm_num at * <;> omega
  have hall (k : ℤ) (hk : ∀ i, k ≤ H i)
      (hsum : H 0 + H 1 + H 2 + H 3 = 4 * k) (i : Fin 4) : H i = k := by
    have h0 := hk 0
    have h1 := hk 1
    have h2 := hk 2
    have h3 := hk 3
    fin_cases i
    · change H 0 = k
      omega
    · change H 1 = k
      omega
    · change H 2 = k
      omega
    · change H 3 = k
      omega
  rcases hZcases with h | h | h
  · have hk (i : Fin 4) : 30 ≤ H i := by
      have hlow := hl i
      have hmod := hm i
      have heven := he i
      omega
    exact Or.inl ⟨h, hall 30 hk (by omega)⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h, hall 28 hl (by omega)⟩)

-- The only projected edges in direction zero are (0,1), (10,11) and (12,13).
private def firstEdges (a : Fin 4 → ℤ) (m : Fin 6 → ℤ) : ℤ :=
  occupied (a 0) * occupied (m 0) + occupied (a 2) * occupied (m 3) +
    occupied (a 3) * occupied (m 4)

private def cutMidpoint (side : Fin 4 → Bool) (e : Fin 6) : ℤ :=
  (if side (endpoints e).1 then 1 else 0) - (if side (endpoints e).2 then 1 else 0)

private def zeroCutPair (z : Q 9 → ℤ) (y : Q 5) : ℤ :=
  countIf (oddCount z y = 0 ∧ evenCount (fun i => evenLabel z i y) = 2)

private def skewTerm (r s : ℤ) (dr ds : ℤ) : ℤ := dr * s - r * ds

private def cutSkew (a : Fin 4 → ℤ) (side : Fin 4 → Bool) (i : Fin 4) (e : Fin 6) : ℤ :=
  let m := cutMidpoint side e
  skewTerm (a i) m (3 * a i - cutPotential side i)
    (a (endpoints e).1 - a (endpoints e).2 - 3 * m)

-- Four cut bits determine all midpoints. The exterior even sum and the positive
-- selected horizontal edges restrict the four remaining ternary labels.
private theorem cut_parity_table :
    ∀ (b₀ b₁ b₂ b₃ : Bool) (t₀ t₁ t₂ t₃ : Fin 3),
      let side : Fin 4 → Bool := ![b₀, b₁, b₂, b₃]
      let a : Fin 4 → ℤ := ![ternary t₀, ternary t₁, ternary t₂, ternary t₃]
      let m := cutMidpoint side
      (∑ i, a i) = 0 →
      (∀ i, a i = 0 ∨ cutPotential side i = 0 ∨ 0 < a i * cutPotential side i) →
      2 ∣ firstEdges a m + cutSkew a side 0 3 + cutSkew a side 2 4 + cutSkew a side 3 5 -
        countIf ((∑ e, occupied (m e)) = 0 ∧ evenCount a = 2) := by
  decide +kernel

private theorem cut_parity {a : Fin 4 → ℤ} (side : Fin 4 → Bool)
    (hu : ∀ i, a i = 0 ∨ a i = 1 ∨ a i = -1) (hs : (∑ i, a i) = 0)
    (hp : ∀ i, a i = 0 ∨ cutPotential side i = 0 ∨ 0 < a i * cutPotential side i) :
    let m := cutMidpoint side
    2 ∣ firstEdges a m + cutSkew a side 0 3 + cutSkew a side 2 4 + cutSkew a side 3 5 -
      countIf ((∑ e, occupied (m e)) = 0 ∧ evenCount a = 2) := by
  obtain ⟨t₀, h₀⟩ := exists_ternary (hu 0)
  obtain ⟨t₁, h₁⟩ := exists_ternary (hu 1)
  obtain ⟨t₂, h₂⟩ := exists_ternary (hu 2)
  obtain ⟨t₃, h₃⟩ := exists_ternary (hu 3)
  have ha : (![ternary t₀, ternary t₁, ternary t₂, ternary t₃] : Fin 4 → ℤ) = a := by
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  have hb : (![side 0, side 1, side 2, side 3] : Fin 4 → Bool) = side := by
    funext i
    fin_cases i <;> rfl
  have h := cut_parity_table (side 0) (side 1) (side 2) (side 3) t₀ t₁ t₂ t₃
  dsimp only at h
  rw [ha, hb] at h
  exact h hs hp

private def midpointLabel (z : Q 9 → ℤ) (e : Fin 6) (y : Q 5) : ℤ :=
  fiber z y (pattern (midpointCode e))

private def skewPairing (z : Q 9 → ℤ) (i : Fin 4) (e : Fin 6) (y : Q 5) : ℤ :=
  skewTerm (evenLabel z i y) (midpointLabel z e y)
    (signedRow (evenLabel z i) y) (signedRow (midpointLabel z e) y)

private theorem sum_skewPairing (z : Q 9 → ℤ) (i : Fin 4) (e : Fin 6) :
    (∑ y, skewPairing z i e y) = 0 := by
  simp only [skewPairing, skewTerm, sum_sub_distrib,
    signedRow_pairing_symmetric (evenLabel z i) (midpointLabel z e), sub_self]

private theorem fiber_firstEdges {z : Q 9 → ℤ} {y : Q 5}
    (hf : ∀ x ∉ tenProjection, fiber z y x = 0) :
    firstEdges (fun i => evenLabel z i y) (fun e => midpointLabel z e y) =
      ∑ i, occupied (evenLabel z i y) *
        occupied (fiber z y (flip (pattern (vertexCode i)) 0)) := by
  have h0 : flip (pattern (vertexCode 0)) 0 = pattern (midpointCode 0) := by decide +kernel
  have h1 : flip (pattern (vertexCode 1)) 0 = pattern 8 := by decide +kernel
  have h2 : flip (pattern (vertexCode 2)) 0 = pattern (midpointCode 3) := by decide +kernel
  have h3 : flip (pattern (vertexCode 3)) 0 = pattern (midpointCode 4) := by decide +kernel
  have h8 : pattern 8 ∉ tenProjection := by decide +kernel
  simp only [firstEdges, midpointLabel, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc,
    h0, h1, h2, h3, hf _ h8, show occupied 0 = 0 by rfl, mul_zero, add_zero]
  ring

open Classical in
private theorem fiber_parity {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (ha : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y)
    (y : Q 5) :
    2 ∣ firstEdges (fun i => evenLabel z i y) (fun e => midpointLabel z e y) +
      skewPairing z 0 3 y + skewPairing z 2 4 y + skewPairing z 3 5 y - zeroCutPair z y := by
  let a (i : Fin 4) := evenLabel z i y
  have hs (x : Q 4) (hx : x ∉ tenProjection) :=
    fiber_and_signedRow_supported hz hrow y (hP.symm ▸ hx)
  have hf (x : Q 4) (hx : x ∉ tenProjection) := (hs x hx).1
  have hr (x : Q 4) (hx : x ∉ tenProjection) := (hs x hx).2
  have huv (i : Fin 4) : a i = 0 ∨ a i = 1 ∨ a i = -1 :=
    label_values hu hz (join (pattern (vertexCode i)) y)
  have hsum : (∑ i, a i) = 0 := by
    have h := (exterior_constraints hf hr).2.2.2
    simpa [a, evenLabel, vertexCode, Fin.sum_univ_succ, add_assoc] using h
  obtain ⟨hm, _, level, side, hl, _⟩ := midpoint_cut hf hr (fun e => by
    rcases label_values hu hz (join (pattern (midpointCode e)) y) with h | h | h <;>
      change |z _| ≤ 1 <;> simp [h])
  have hmid (e : Fin 6) : midpointLabel z e y = cutMidpoint side e := by
    have h := congrFun hm e
    change midpointLabel z e y = _ at h
    rw [transpose_mulVec, hl, hl] at h
    unfold cutMidpoint
    omega
  have hpos (i : Fin 4) :
      a i = 0 ∨ cutPotential side i = 0 ∨ 0 < a i * cutPotential side i := by
    rw [← cutPotential_eq hl]
    by_cases haz : a i = 0
    · exact Or.inl haz
    by_cases hc : cScaled z i y = 0
    · exact Or.inr (Or.inl hc)
    have h := q9_signed_row_split hrow (pattern (vertexCode i)) y
    simp only [pattern_parities.1, one_mul] at h
    change 3 * evenLabel z i y = signedRow (fiber z y) (pattern (vertexCode i)) +
      signedRow (evenLabel z i) y at h
    rw [ha] at h
    have he : signedRow (fiber z y) (pattern (vertexCode i)) = cScaled z i y := by omega
    have ht := even_mul_center hreg hu hz hrow haz he
    refine Or.inr (Or.inr (lt_of_le_of_ne ?_ (Ne.symm (mul_ne_zero haz hc))))
    change 0 ≤ evenLabel z i y * cScaled z i y
    rw [ht]
    exact sum_nonneg (fun j _ => by unfold occupied; split <;> omega)
  have hmrow (e : Fin 6) : signedRow (midpointLabel z e) y =
      a (endpoints e).1 - a (endpoints e).2 - 3 * cutMidpoint side e := by
    have h := q9_signed_row_split hrow (pattern (midpointCode e)) y
    simp only [pattern_parities.2, neg_one_mul] at h
    change 3 * midpointLabel z e y =
      signedRow (fiber z y) (pattern (midpointCode e)) - signedRow (midpointLabel z e) y at h
    have hh := congrFun (signed_row_blocks hf).2 e
    rw [transpose_mulVec] at hh
    change signedRow (fiber z y) (pattern (midpointCode e)) = a _ - a _ at hh
    rw [hh, hmid] at h
    omega
  have hskew (i : Fin 4) (e : Fin 6) : skewPairing z i e y = cutSkew a side i e := by
    simp only [skewPairing, cutSkew, ha, hmrow, hmid, cutPotential_eq hl, a]
  have ho : oddCount z y = ∑ e, occupied (cutMidpoint side e) :=
    sum_congr rfl (fun e _ => congrArg occupied (hmid e))
  simp only [hskew, zeroCutPair, ho, show (fun i => evenLabel z i y) = a from rfl]
  rw [show (fun e => midpointLabel z e y) = cutMidpoint side from funext hmid]
  exact cut_parity side huv hsum hpos

open Classical in
private theorem zero_cut_occupation_dvd_four {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (ha : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y)
    (ht : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y)) :
    4 ∣ zeroCutOccupation z := by
  have hedges : (∑ y, firstEdges (fun i => evenLabel z i y) (fun e => midpointLabel z e y)) =
      12 := by
    calc
      _ = ∑ y, ∑ i, occupied (evenLabel z i y) *
          occupied (fiber z y (flip (pattern (vertexCode i)) 0)) :=
        sum_congr rfl (fun y _ => fiber_firstEdges
          (fun x hx => (fiber_and_signedRow_supported hz hrow y (hP.symm ▸ hx)).1))
      _ = (directionEdges C ((0 : Fin 4).castAdd 5) : ℤ) := horizontal_endpoint_sum hP hu hz 0
      _ = 12 := by rw [twelve_edges hsize hreg hb]; rfl
  have hparity := dvd_sum (s := (univ : Finset (Q 5)))
    (fun y _ => fiber_parity hreg hP hu hz hrow ha y)
  simp only [sum_sub_distrib, sum_add_distrib, sum_skewPairing, hedges, add_zero] at hparity
  let four (y : Q 5) := countIf (oddCount z y = 0 ∧ evenCount (fun i => evenLabel z i y) = 4)
  have hfiber (y : Q 5) : (if oddCount z y = 0 then evenCount (fun i => evenLabel z i y) else 0) =
      2 * zeroCutPair z y + 4 * four y := by
    rcases ht y with ⟨_, ho, he⟩ | ⟨i, sign, ho, _, _⟩ | ⟨ho, _, _, _⟩
    · rcases he with he | he | he <;>
        simp [zeroCutPair, four, countIf, ho, he]
    · simp [zeroCutPair, four, countIf, ho]
    · simp [zeroCutPair, four, countIf, ho]
  have htotal : zeroCutOccupation z = 2 * (∑ y, zeroCutPair z y) + 4 * (∑ y, four y) := by
    simp only [zeroCutOccupation, hfiber, sum_add_distrib, ← mul_sum]
  omega

open Classical in
/-- With all four K4 star halves at least 28, zero cuts contain either zero
even vertices with four halves of size 30, or eight with four halves of size 28. -/
theorem balanced_zero_cut_occupation {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalves : ∀ i, 28 ≤ (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      (∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
        signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y) ∧
      (∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y)) ∧
      ((zeroCutOccupation z = 0 ∧ ∀ i,
          (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card = 30) ∨
        (zeroCutOccupation z = 8 ∧ ∀ i,
          (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card = 28)) := by
  obtain ⟨z, hu, hz, hrow, hrows, ht⟩ := balanced_cut_types hreg hb hP
  have ha (i : Fin 4) (y : Q 5) := (hrows i y).1
  obtain ⟨hn, _, hodd, hsum⟩ := occupation_totals hsize hreg hb hP hu hz hrow ha ht
  let H (i : Fin 4) := ∑ y, starCount z i y
  have hcard (i : Fin 4) := star_count_eq_half hP hu hz i
  have hlo (i : Fin 4) : 28 ≤ H i := by
    change 28 ≤ ∑ y, starCount z i y
    rw [hcard]
    exact_mod_cast hhalves i
  have heven (i : Fin 4) : 2 ∣ H i := by
    change 2 ∣ ∑ y, starCount z i y
    have hp := even_iff_two_dvd.mp
      (coordinate_half_even hsize hreg hb ((starAxis i).castAdd 5) (decide (i ≠ 0)))
    rw [hcard]
    exact_mod_cast hp
  have hmod (i : Fin 4) : 6 ∣ 4 * H i - 48 + zeroCutOccupation z :=
    ⟨_, (half_pairing hP hu hz hrow hrows ht hodd i).symm⟩
  have hdvd := zero_cut_occupation_dvd_four hsize hreg hb hP hu hz hrow ha ht
  refine ⟨z, hu, hz, hrow, hrows, ht, ?_⟩
  rcases half_cases H _ hn hsum hlo heven hmod with ⟨h, hh⟩ | h | ⟨h, hh⟩
  · refine Or.inl ⟨h, fun i => ?_⟩
    have hi := (hcard i).symm.trans (hh i)
    exact_mod_cast hi
  · omega
  · refine Or.inr ⟨h, fun i => ?_⟩
    have hi := (hcard i).symm.trans (hh i)
    exact_mod_cast hi

#print axioms coordinate_half_even
#print axioms balanced_zero_cut_occupation

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4ZeroCutArithmetic
