import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixNormalizeProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning

/-! The integer switching equations used by the finite Q9 support model. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced switchingVector flip_adj directionEdges
  directionEndpoints direction_edge_count)
local notation "flip" => BalancedCriticalSpectrum.flip
attribute [local instance] Classical.propDecidable
open private huangMatrix cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private paritySide parity_bipartite parity_union from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private directions mem_directions directions_card exterior_even from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound sixty_six_edge_weight_inequality sum_ofFn_int from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private distance_seven_agreement_excludes_minority from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerWeightsProbe
open private agreeing_coordinate_unused unusedDirections unused_card antipode hamming_antipode_add
  matching_coordinate_pair_unused from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe
open private matrix_flip_prefix from D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
open private theta theta_flip theta_unit prod_true_sign from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
open private matrix_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- The TRUE-prefix sign on the edge that flips coordinate `i`. -/
def truePrefixSign {n : ℕ} (x : Q n) (i : Fin n) : ℤ :=
  (-1) ^ ((univ : Finset (Fin n)).filter (fun j => j < i ∧ x j = true)).card

private lemma matrix_true_prefix {n : ℕ} (x : Q n) (i : Fin n) :
    huangMatrix n x (flip x i) =
      theta x * theta (flip x i) * (truePrefixSign x i : ℝ) := by
  classical
  rw [matrix_flip_prefix, theta_flip]
  have hfactor (j : Fin n) :
      (if j < i ∧ x j = false then (-1 : ℝ) else 1) =
        (if j < i then (-1 : ℝ) else 1) *
          (if j < i ∧ x j = true then (-1 : ℝ) else 1) := by
    by_cases hj : j < i <;> cases x j <;> simp [hj]
  simp_rw [hfactor]
  rw [prod_mul_distrib, prod_true_sign, prod_true_sign]
  have hcount : ((univ : Finset (Fin n)).filter (· < i)).card = i.val := by
    rw [show univ.filter (· < i) = Iio i by ext j; simp, Fin.card_Iio]
  rw [hcount]
  push_cast [truePrefixSign]
  rfl

/-- A balanced cubic support has integral TRUE-prefix switching signs and
obeys the signed neighbor equation at every vertex of the nine-cube. -/
theorem q9_integral_true_prefix_switching {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ z : Q 9 → ℤ,
      (∀ x ∈ C, z x = 1 ∨ z x = -1) ∧ (∀ x ∉ C, z x = 0) ∧
      (∀ x ∈ C, ∀ i : Fin 9, flip x i ∈ C →
        truePrefixSign x i = z x * z (flip x i)) ∧
      ∀ x, (∑ i : Fin 9, truePrefixSign x i * z (flip x i)) = 3 * z x := by
  classical
  obtain ⟨sigma, hs⟩ := hb
  let z : Q 9 → ℤ := fun x =>
    if x ∈ C then (if theta x * sigma x = 1 then 1 else -1) else 0
  have hunit (x : Q 9) (hx : x ∈ C) : theta x * sigma x = 1 ∨ theta x * sigma x = -1 := by
    rcases theta_unit x with h | h <;> rcases hs.1 x hx with h' | h' <;> simp [h, h']
  have hz (x : Q 9) : (z x : ℝ) = theta x * switchingVector C sigma x := by
    by_cases hx : x ∈ C
    · rcases hunit x hx with h | h <;> norm_num [z, switchingVector, hx, h]
    · simp [z, switchingVector, hx]
  refine ⟨z, ?_, fun x hx => by simp [z, hx], ?_, ?_⟩
  · intro x hx
    simp only [z, ite_eq_left hx]
    split <;> simp
  · intro x hx i hy
    have he := matrix_true_prefix x i
    rw [hs.2 x hx _ hy (flip_adj x i)] at he
    have hh : (truePrefixSign x i : ℝ) = (z x : ℝ) * (z (flip x i) : ℝ) := by
      rw [hz, hz, switchingVector, switchingVector, ite_eq_left hx, ite_eq_left hy]
      rcases theta_unit x with h | h <;> rcases theta_unit (flip x i) with h' | h' <;>
        rw [h, h'] at he ⊢ <;> linarith
    exact_mod_cast hh
  · intro x
    have h := congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C sigma hreg hs) x
    change (huangMatrix 9).mulVec (switchingVector C sigma) x =
      3 * switchingVector C sigma x at h
    rw [matrix_row] at h
    change (∑ i : Fin 9, huangMatrix 9 x (flip x i) *
      switchingVector C sigma (flip x i)) = 3 * switchingVector C sigma x at h
    have hterm (i : Fin 9) : (truePrefixSign x i : ℝ) * (z (flip x i) : ℝ) =
        theta x * (huangMatrix 9 x (flip x i) * switchingVector C sigma (flip x i)) := by
      rw [hz]
      rw [matrix_true_prefix]
      rcases theta_unit x with ht | ht <;> simp [ht] <;> ring
    have heq : (∑ i : Fin 9, (truePrefixSign x i : ℝ) * (z (flip x i) : ℝ)) = 3 * (z x : ℝ) := by
      simp_rw [hterm]
      rw [← mul_sum, h, hz]
      ring
    exact_mod_cast heq

#print axioms q9_integral_true_prefix_switching

private lemma cubic_parity_half_card {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (b : Bool) :
    (C.filter (fun x => cubeParity x = b)).card = 33 := by
  have hdegrees := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite C)
  simp only [hreg.degree_eq, sum_const, smul_eq_mul] at hdegrees
  have hunion := congrArg Finset.card (parity_union C)
  rw [card_union_of_disjoint (by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Bool.false_ne_true ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)),
    card_univ, show Fintype.card (C : Set (Q 9)) = 66 by simpa using hC] at hunion
  have himage : (paritySide C b).image Subtype.val = C.filter (fun x => cubeParity x = b) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨y.property, (mem_filter.mp hy).2⟩
    · intro hx
      exact mem_image.mpr
        ⟨⟨x, (mem_filter.mp hx).1⟩, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩, rfl⟩
  rw [← himage, card_image_of_injective _ Subtype.val_injective]
  cases b <;> omega

private lemma distance_seven_agreement_count {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    {x : Q 9} (hx : x ∈ C) (i : Fin 9) :
    let count := (C.filter (fun y => hammingDist x y = 7 ∧ x i = y i)).card
    Even count ∧ count ≤ 4 := by
  dsimp only
  let v := flip (antipode x) i
  have hnear (y : Q 9) (hy : y ∈ C) :
      (hypercube 9).Adj v y ↔ hammingDist x y = 7 ∧ x i = y i := by
    have hdist := hamming_antipode_add x y
    have hbound := hd x hx y hy
    change hammingDist x y + (diff (antipode x) y).card = 9 at hdist
    change (diff (flip (antipode x) i) y).card = 1 ↔ _
    rw [diff_flip]
    by_cases hagree : x i = y i
    · have hmem : i ∈ diff (antipode x) y := by
        cases h : x i <;> simp [diff, antipode, ← hagree, h]
      have he := card_erase_add_one hmem
      rw [ite_eq_left hmem]
      simp only [hagree, and_true]
      omega
    · have hmem : i ∉ diff (antipode x) y := by
        cases h : x i <;> cases hy' : y i <;> simp_all [diff, antipode]
      rw [ite_eq_right hmem, card_insert_of_notMem hmem]
      simp only [hagree, and_false, iff_false]
      omega
  have hcount : (directions C v).card =
      (C.filter (fun y => hammingDist x y = 7 ∧ x i = y i)).card := by
    rw [directions_card]
    congr 1
    ext y
    simp only [mem_filter]
    exact and_congr_right (hnear y)
  have hv : v ∉ C := by
    intro hv
    have h := hamming_antipode_add x v
    have hflip : hammingDist (antipode x) v = 1 := flip_adj _ _
    have hbound := hd x hx v hv
    omega
  rw [← hcount]
  have heven := exterior_even C hreg hb v hv
  refine ⟨heven, ?_⟩
  have hpair (j : Fin 9) (hj : j ∈ directions C v) :
      i ∈ unusedDirections C x ∧ j ∈ (unusedDirections C x).erase i := by
    have hselected := (mem_directions C v j).mp hj
    have hij : i ≠ j := by
      rintro rfl
      have ha : antipode x ∈ C := by
        simpa [v, BalancedCriticalSpectrum.flip_flip] using hselected
      have h := hamming_antipode_add x (antipode x)
      have hbound := hd x hx _ ha
      rw [hammingDist_self] at h
      omega
    have h := matching_coordinate_pair_unused hd hij hselected
    exact ⟨h.1, mem_erase.mpr ⟨hij.symm, h.2⟩⟩
  by_cases hpos : (directions C v).Nonempty
  · obtain ⟨j, hj⟩ := hpos
    have hle := card_le_card (fun j hj => (hpair j hj).2)
    rw [card_erase_of_mem (hpair j hj).1, unused_card hreg hx] at hle
    obtain ⟨k, hk⟩ := heven
    omega
  · rw [not_nonempty_iff_eq_empty.mp hpos, card_empty]
    decide

/-- The support of a 66-point balanced cubic component gives a candidate profile
and integer labels satisfying the signed equations and distance constraints. -/
theorem q9_sixty_six_normalized_signed_constraints {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ) (z : Q 9 → ℤ),
      List.ofFn r ∈ sixtySixCandidateProfiles ∧ S.card = 66 ∧
      ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced S ∧
      (∀ b, (S.filter (fun x => cubeParity x = b)).card = 33) ∧
      (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      (∀ i, directionEdges S i = 11) ∧
      (∀ x ∈ S, ∀ y ∈ S, hammingDist x y ≤ 7) ∧
      (∀ x ∈ S, (∑ i, if x i then r i else 0) ≤ ((∑ i, r i) - 4) / 2) ∧
      (∀ x ∈ S, (shell S x 7).card ≤ 8 ∧
        2 * (∑ i, if x i then r i else 0) + 12 ≤ (∑ i, r i) + (shell S x 7).card) ∧
      (∀ x ∈ S, ∀ y ∈ S, hammingDist x y = 7 → ∀ i, x i = y i →
        flip x i ∉ S ∧ (x i = true → r i ≤ 1)) ∧
      (∀ x ∈ S, ∀ i, let count := (S.filter (fun y => hammingDist x y = 7 ∧ x i = y i)).card
        Even count ∧ count ≤ 4) ∧
      (∀ x ∈ S, z x = 1 ∨ z x = -1) ∧ (∀ x ∉ S, z x = 0) ∧
      (∀ x ∈ S, ∀ i, flip x i ∈ S → truePrefixSign x i = z x * z (flip x i)) ∧
      ∀ x, (∑ i, truePrefixSign x i * z (flip x i)) = 3 * z x := by
  obtain ⟨S, r, hS, hregS, hbS, hd, hmono, hr, hhalf, hw, hm⟩ :=
    exists_sorted_minority_cube_support hC hreg hb
      (huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb)
  obtain ⟨z, hsign, hzero, hedge, hsum⟩ := q9_integral_true_prefix_switching hregS hbS
  refine ⟨S, r, z, sorted_deficits_mem_sixtySixCandidateProfiles r hmono hr hm,
    hS, hregS, hbS, cubic_parity_half_card hS hregS, hhalf, ?_, hd, hw, ?_, ?_,
    fun _ hx i => distance_seven_agreement_count hregS hbS hd hx i, hsign, hzero, hedge, hsum⟩
  · intro i
    have h := direction_edge_count (d := 3) S hregS hbS i
    omega
  · intro x hx
    exact ⟨sixty_six_distance_seven_le_eight hS hregS hbS hd hx,
      coordinate_profile_weight_bound hS hregS hbS (fun _ => true) r hhalf hx⟩
  · intro x hx y hy hxy i hi
    have hunused := agreeing_coordinate_unused hd hy hxy hi
    refine ⟨fun hflip => (mem_sdiff.mp hunused).2 ((mem_directions S x i).mpr hflip), ?_⟩
    exact distance_seven_agreement_excludes_minority hS hregS hbS hd
      (fun _ => true) r hr hhalf hx hy hxy hi

#print axioms q9_sixty_six_normalized_signed_constraints

private lemma selected_coordinate_count_bound {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (r : Fin 9 → ℤ)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33)
    (J : Finset (Fin 9)) (K : ℤ)
    (hK : ∀ x ∈ C, (∑ i ∈ J, if x i then (1 : ℤ) else 0) ≤ K) :
    ∑ i ∈ J, (110 - 6 * r i) ≤ 198 * K := by
  let a (i : Fin 9) : ℤ := if i ∈ J then 1 else 0
  let t (x : Q 9) (i : Fin 9) : ℤ := if x i then a i else 0
  let w (x : Q 9) : ℤ := ∑ i, t x i
  let g (x : Q 9) : ℤ := K - w x
  have hw (x : Q 9) : w x = ∑ i ∈ J, if x i then (1 : ℤ) else 0 := by
    calc
      w x = ∑ i ∈ J, t x i := (sum_subset (subset_univ J) (by
        intro i _ hi
        simp [t, a, hi])).symm
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        simp [t, a, hi]
  have hn (x : Q 9) (hx : x ∈ C) : 0 ≤ g x := by
    dsimp only [g]
    exact sub_nonneg.mpr ((hw x).trans_le (hK x hx))
  have hlocal (i : Fin 9) (x : Q 9) (hx : x ∈ directionEndpoints C i) :
      a i ≤ g x + g (flip x i) := by
    have hxC := (mem_filter.mp hx).1
    have hfC := (mem_filter.mp hx).2
    have hsplit (y : Q 9) :
        w y = (∑ j ∈ (univ : Finset (Fin 9)).erase i, t y j) + t y i :=
      (sum_erase_add _ _ (mem_univ i)).symm
    have hs : (∑ j ∈ (univ : Finset (Fin 9)).erase i, t (flip x i) j) =
        ∑ j ∈ (univ : Finset (Fin 9)).erase i, t x j := by
      apply sum_congr rfl
      intro j hj
      simp [t, BalancedCriticalSpectrum.flip, (mem_erase.mp hj).1]
    have hdiff : g (flip x i) - g x = t x i - t (flip x i) i := by
      dsimp [g]
      rw [hsplit x, hsplit (flip x i), hs]
      ring
    cases hi : x i <;>
      simp [t, BalancedCriticalSpectrum.flip_apply_same, hi] at hdiff <;>
      linarith [hn x hxC, hn _ hfC]
  have hedge := sixty_six_edge_weight_inequality hC hreg hb a g hlocal
  have ha : (∑ i, a i) = (J.card : ℤ) := by
    change (∑ i, if i ∈ J then (1 : ℤ) else 0) = _
    have hJ : (univ : Finset (Fin 9)).filter (· ∈ J) = J := by
      ext i
      simp
    rw [← sum_filter, hJ, sum_const]
    simp
  have htotal : (∑ x ∈ C, w x) = ∑ i ∈ J, (33 - 2 * r i) := by
    simp_rw [hw]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← sum_filter, sum_const]
    simpa using eq_sub_of_add_eq (hhalf i)
  have hgap : (∑ x ∈ C, g x) = 66 * K - ∑ i ∈ J, (33 - 2 * r i) := by
    dsimp only [g]
    rw [sum_sub_distrib, sum_const, hC, nsmul_eq_mul, htotal]
    norm_num
  have heq : (∑ i ∈ J, (110 - 6 * r i)) =
      11 * J.card + 3 * ∑ i ∈ J, (33 - 2 * r i) := by
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    ring
  rw [ha, hgap] at hedge
  rw [heq]
  linarith

/-- Eight or more deficit-five coordinates force a point with at least
`52 - ∑ i, r i` distance-seven partners. In particular, a uniform cap of
six rules out all such profiles. -/
theorem q9_sixty_six_many_deficit_five_force_partners {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (r : Fin 9 → ℤ) (hr : ∀ i, 0 ≤ r i)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33)
    (hmany : 8 ≤ (univ.filter (fun i => r i = 5)).card) :
    ∃ x ∈ C, 52 ≤ (∑ i, r i) + (shell C x 7).card := by
  let a (i : Fin 9) : ℤ := if r i = 5 then 1 else 0
  let t (x : Q 9) (i : Fin 9) : ℤ := if x i then a i else 0
  let w (x : Q 9) : ℤ := ∑ i, t x i
  have hcount : 8 ≤ ∑ i, a i := by
    have hsum : ∑ i, a i = ((univ.filter (fun i => r i = 5)).card : ℤ) := by
      dsimp [a]
      rw [← sum_filter, sum_const]
      simp
    rw [hsum]
    exact_mod_cast hmany
  have htotal : (∑ x ∈ C, w x) = 23 * ∑ i, a i := by
    dsimp only [w, t]
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    by_cases hi : r i = 5
    · have hcard := hhalf i
      rw [hi] at hcard
      simp only [a, ite_eq_left hi]
      linarith
    · simp [a, hi]
  have hroot : ∃ x ∈ C, 4 ≤ w x := by
    by_contra! h
    let g (x : Q 9) : ℤ := 3 - w x
    have hn (x : Q 9) (hx : x ∈ C) : 0 ≤ g x := by
      dsimp [g]
      have := h x hx
      omega
    have hlocal (i : Fin 9) (x : Q 9) (hx : x ∈ directionEndpoints C i) :
        a i ≤ g x + g (flip x i) := by
      have hxC := (mem_filter.mp hx).1
      have hfC := (mem_filter.mp hx).2
      have hsplit (y : Q 9) :
          w y = (∑ j ∈ (univ : Finset (Fin 9)).erase i, t y j) + t y i :=
        (sum_erase_add _ _ (mem_univ i)).symm
      have hs : (∑ j ∈ (univ : Finset (Fin 9)).erase i, t (flip x i) j) =
          ∑ j ∈ (univ : Finset (Fin 9)).erase i, t x j := by
        apply sum_congr rfl
        intro j hj
        simp [t, BalancedCriticalSpectrum.flip, (mem_erase.mp hj).1]
      have hdiff : g (flip x i) - g x = t x i - t (flip x i) i := by
        dsimp [g]
        rw [hsplit x, hsplit (flip x i), hs]
        ring
      cases hi : x i <;>
        simp [t, BalancedCriticalSpectrum.flip_apply_same, hi] at hdiff <;>
        linarith [hn x hxC, hn _ hfC]
    have hedge := sixty_six_edge_weight_inequality hC hreg hb a g hlocal
    have hgap : (∑ x ∈ C, g x) = 198 - 23 * ∑ i, a i := by
      dsimp only [g]
      rw [sum_sub_distrib, sum_const, hC, nsmul_eq_mul, htotal]
      norm_num
    rw [hgap] at hedge
    linarith
  obtain ⟨x, hx, hw⟩ := hroot
  have hwle : 5 * w x ≤ ∑ i, if x i then r i else 0 := by
    dsimp only [w, t]
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    cases hi : x i
    · simp
    · by_cases hri : r i = 5
      · simp [a, hri]
      · simpa [a, hri] using hr i
  have hpartners := coordinate_profile_weight_bound hC hreg hb (fun _ => true) r hhalf hx
  have hweight : (∑ i, if x i = true then r i else 0) =
      ∑ i, if x i then r i else 0 := rfl
  rw [hweight] at hpartners
  exact ⟨x, hx, by linarith⟩

#print axioms q9_sixty_six_many_deficit_five_force_partners

/-- Candidate deficits after imposing the distance-seven bound for profiles
with eight or more deficit-five coordinates. -/
def sixtySixProfilesAfterPartnerBound : List (List ℤ) :=
  sixtySixCandidateProfiles.filter fun profile =>
    decide ((profile.map fun r => if r = 5 then (1 : ℤ) else 0).sum < 8 ∨ 44 ≤ profile.sum)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The kernel reduces both filters on the enumerated deficit profiles.
theorem sixtySixProfilesAfterPartnerBound_length :
    sixtySixProfilesAfterPartnerBound.length = 247 := by
  decide +kernel

/-- Every 66-point support gives one of the 247 remaining deficit profiles. -/
theorem q9_sixty_six_mem_profiles_after_partner_bound {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterPartnerBound := by
  obtain ⟨S, r, hS, hregS, hbS, hd, hmono, hr, hhalf, _, hm⟩ :=
    exists_sorted_minority_cube_support hC hreg hb
      (huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb)
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterPartnerBound, List.mem_filter, decide_eq_true_eq]
  refine ⟨sorted_deficits_mem_sixtySixCandidateProfiles r hmono hr hm, ?_⟩
  rw [List.map_ofFn, sum_ofFn_int, sum_ofFn_int]
  simp only [Function.comp_apply]
  have hcount : (∑ i : Fin 9, if r i = 5 then (1 : ℤ) else 0) =
      ((univ.filter (fun i => r i = 5)).card : ℤ) := by
    rw [← sum_filter, sum_const]
    simp
  rw [hcount]
  by_cases h : 8 ≤ (univ.filter (fun i => r i = 5)).card
  · right
    obtain ⟨x, hx, hlower⟩ := q9_sixty_six_many_deficit_five_force_partners hS hregS hbS
      r (fun i => (hr i).1) hhalf h
    have hupper : ((shell S x 7).card : ℤ) ≤ 8 := by
      exact_mod_cast sixty_six_distance_seven_le_eight hS hregS hbS hd hx
    omega
  · left
    exact_mod_cast Nat.lt_of_not_ge h

#print axioms sixtySixProfilesAfterPartnerBound_length
#print axioms q9_sixty_six_mem_profiles_after_partner_bound

private lemma prefix_weight_le_of_card_le {r : Fin 9 → ℤ} (hmono : Monotone r)
    (hr : ∀ i, 0 ≤ r i) {a b : Fin 9} {T : Finset (Fin 9)}
    (hT : T ⊆ Ici a) (hcard : (Icc a b).card ≤ T.card) :
    ∑ i ∈ Icc a b, r i ≤ ∑ i ∈ T, r i := by
  let P := Icc a b
  have hP := card_sdiff_add_card_inter P T
  have hQ := card_sdiff_add_card_inter T P
  rw [inter_comm T P] at hQ
  have hdiff : ((P \ T).card : ℤ) ≤ (T \ P).card := by
    change P.card ≤ T.card at hcard
    exact_mod_cast (show (P \ T).card ≤ (T \ P).card by omega)
  have hupper : ∑ i ∈ P \ T, r i ≤ ((P \ T).card : ℤ) * r b := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => hmono (mem_Icc.mp (mem_sdiff.mp hi).1).2
  have hlower : ((T \ P).card : ℤ) * r b ≤ ∑ i ∈ T \ P, r i := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro i hi
    obtain ⟨hiT, hiP⟩ := mem_sdiff.mp hi
    exact hmono (le_of_not_ge fun hib => hiP (mem_Icc.mpr ⟨mem_Ici.mp (hT hiT), hib⟩))
  have hsumP := sum_inter_add_sum_sdiff P T r
  have hsumT := sum_inter_add_sum_sdiff T P r
  rw [inter_comm T P] at hsumT
  change ∑ i ∈ P, r i ≤ ∑ i ∈ T, r i
  linarith [mul_le_mul_of_nonneg_right hdiff (hr b)]

private def suffixConflict (r : Fin 9 → ℤ) (K : ℤ) (a b : Fin 9) : Prop :=
  a ≤ b ∧ K < ∑ i ∈ Icc a b, r i ∧
    198 * ((b.val - a.val : ℕ) : ℤ) < ∑ i ∈ Ici a, (110 - 6 * r i)

private instance (r : Fin 9 → ℤ) (K : ℤ) (a b : Fin 9) :
    Decidable (suffixConflict r K a b) := by
  unfold suffixConflict
  infer_instance

private lemma no_suffix_conflict {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    {r : Fin 9 → ℤ} (hmono : Monotone r) (hr : ∀ i, 0 ≤ r i)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33)
    {K : ℤ} (hK : ∀ x ∈ C, (∑ i, if x i then r i else 0) ≤ K)
    (a b : Fin 9) : ¬ suffixConflict r K a b := by
  rintro ⟨hab, hprefix, hsum⟩
  have hbound (x : Q 9) (hx : x ∈ C) :
      (∑ i ∈ Ici a, if x i then (1 : ℤ) else 0) ≤ ((b.val - a.val : ℕ) : ℤ) := by
    let T := (Ici a).filter (fun i => x i = true)
    rw [← sum_filter, sum_const]
    simp only [nsmul_eq_mul, mul_one]
    change (T.card : ℤ) ≤ _
    suffices hcard : T.card ≤ b.val - a.val by exact_mod_cast hcard
    by_contra! hcard
    have hp : (Icc a b).card ≤ T.card := by
      rw [Fin.card_Icc]
      change a.val ≤ b.val at hab
      omega
    have hw := prefix_weight_le_of_card_le hmono hr (filter_subset _ _) hp
    have htotal : ∑ i ∈ T, r i ≤ ∑ i, if x i then r i else 0 := by
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
      · intro i _ _
        exact hr i
    linarith [hK x hx]
  have h := selected_coordinate_count_bound hC hreg hb r hhalf (Ici a)
    ((b.val - a.val : ℕ) : ℤ) hbound
  linarith

private def hasSuffixConflict (profile : List ℤ) : Bool :=
  let r := fun i : Fin 9 => profile[i.val]?.getD 0
  let K := (profile.sum - 4) / 2
  (List.finRange 9).any fun a => (List.finRange 9).any fun b =>
    decide (suffixConflict r K a b)

/-- Sorted deficit profiles surviving the restrictions on every suffix of coordinates. -/
def sixtySixProfilesAfterSuffixBounds : List (List ℤ) :=
  sixtySixCandidateProfiles.filter fun profile => !hasSuffixConflict profile

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- The kernel checks all coordinate intervals in the finite profile list.
theorem sixtySixProfilesAfterSuffixBounds_length :
    sixtySixProfilesAfterSuffixBounds.length = 156 := by
  decide +kernel

/-- Every 66-point support gives a profile surviving the suffix bounds. -/
theorem q9_sixty_six_mem_profiles_after_suffix_bounds {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterSuffixBounds := by
  obtain ⟨S, r, hS, hregS, hbS, _, hmono, hr, hhalf, hK, hm⟩ :=
    exists_sorted_minority_cube_support hC hreg hb
      (huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb)
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterSuffixBounds, List.mem_filter]
  refine ⟨sorted_deficits_mem_sixtySixCandidateProfiles r hmono hr hm, ?_⟩
  have he : (fun i : Fin 9 => (List.ofFn r)[i.val]?.getD 0) = r := by
    funext i
    simp only [List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]
  simp only [Bool.not_eq_true', hasSuffixConflict, he, sum_ofFn_int, List.any_eq_false,
    Bool.not_eq_true, decide_eq_false_iff_not]
  intro a _ b _
  exact no_suffix_conflict hS hregS hbS hmono (fun i => (hr i).1) hhalf hK a b

#print axioms sixtySixProfilesAfterSuffixBounds_length
#print axioms q9_sixty_six_mem_profiles_after_suffix_bounds

end D5.S3.Combinatorics.Graph.HypercubeCritical
