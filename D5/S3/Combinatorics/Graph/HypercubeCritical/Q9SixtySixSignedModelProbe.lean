import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixNormalizeProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe

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
open private directions mem_directions directions_card exterior_even regular_directions from
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
    simp only [List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  simp only [Bool.not_eq_true', hasSuffixConflict, he, sum_ofFn_int, List.any_eq_false,
    Bool.not_eq_true, decide_eq_false_iff_not]
  intro a _ b _
  exact no_suffix_conflict hS hregS hbS hmono (fun i => (hr i).1) hhalf hK a b

#print axioms sixtySixProfilesAfterSuffixBounds_length
#print axioms q9_sixty_six_mem_profiles_after_suffix_bounds

private def trueDirections (x : Q 9) : Finset (Fin 9) :=
  univ.filter fun j => x j = true

private lemma trueDirections_injective : Function.Injective trueDirections := by
  intro x y h
  funext j
  have hmem : (x j = true) ↔ (y j = true) := by
    simpa [trueDirections] using (show j ∈ trueDirections x ↔ j ∈ trueDirections y by rw [h])
  cases hx : x j <;> cases hy : y j <;> simp_all

/-- A literal half contained in radius two about its coordinate vertex has
at most nine vertices below the outer layer, and every outer vertex requires
a crossing edge. -/
private lemma thin_half_card_le {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (i : Fin 9) (hthin : ∀ x ∈ C, x i = true → (trueDirections x).card ≤ 3) :
    (C.filter (fun x => x i = true)).card ≤ 9 + directionEdges C i := by
  let H := C.filter (fun x => x i = true)
  let T := H.filter (fun x => (trueDirections x).card ≤ 2)
  let E := C.filter (fun x => x i = false ∧ flip x i ∈ C)
  have hT : T.card ≤ 9 := by
    let erasePivot : Q 9 → Finset (Fin 9) := fun x => (trueDirections x).erase i
    let L := insert ∅ (((univ : Finset (Fin 9)).erase i).image fun j => ({j} : Finset (Fin 9)))
    have hinj : Set.InjOn erasePivot (T : Set (Q 9)) := by
      intro x hx y hy h
      have hx' := (mem_filter.mp (mem_filter.mp hx).1).2
      have hy' := (mem_filter.mp (mem_filter.mp hy).1).2
      have hiX : i ∈ trueDirections x := by simp [trueDirections, hx']
      have hiY : i ∈ trueDirections y := by simp [trueDirections, hy']
      exact trueDirections_injective (by
        simpa only [erasePivot, insert_erase hiX, insert_erase hiY] using congrArg (insert i) h)
    have hsub : T.image erasePivot ⊆ L := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
      have hx' := (mem_filter.mp (mem_filter.mp hx).1).2
      have hiX : i ∈ trueDirections x := by simp [trueDirections, hx']
      have hcard : (erasePivot x).card ≤ 1 := by
        dsimp only [erasePivot]
        rw [card_erase_of_mem hiX]
        have := (mem_filter.mp hx).2
        omega
      by_cases hn : erasePivot x = ∅
      · simp [L, hn]
      · have hpos := card_pos.mpr (nonempty_iff_ne_empty.mpr hn)
        obtain ⟨j, hj⟩ := card_eq_one.mp (by omega : (erasePivot x).card = 1)
        have hji : j ≠ i := by
          have hj' : j ∈ erasePivot x := by simp [hj]
          exact (mem_erase.mp hj').1
        exact mem_insert_of_mem (mem_image.mpr ⟨j, by simp [hji], hj.symm⟩)
    have hL : L.card ≤ 9 := by
      have h := card_insert_le (s := (((univ : Finset (Fin 9)).erase i).image
        (fun j => ({j} : Finset (Fin 9))))) (a := (∅ : Finset (Fin 9)))
      have hi := card_image_le (s := (univ : Finset (Fin 9)).erase i)
        (f := fun j => ({j} : Finset (Fin 9)))
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hi
      dsimp only [L]
      omega
    rw [← card_image_of_injOn hinj]
    exact (card_le_card hsub).trans hL
  have hcross : (H \ T).card ≤ E.card := by
    apply card_le_card_of_injOn (flip · i)
    · intro x hx
      obtain ⟨hxH, hxT⟩ := mem_sdiff.mp hx
      obtain ⟨hxC, hxi⟩ := mem_filter.mp hxH
      have hcard : (trueDirections x).card = 3 := by
        have hu := hthin x hxC hxi
        by_contra! h
        apply hxT
        exact mem_filter.mpr ⟨hxH, by omega⟩
      have hflip : flip x i ∈ C := by
        by_contra hmissing
        have hsub : directions C x ⊆ (trueDirections x).erase i := by
          intro j hj
          have hjC := (mem_directions C x j).mp hj
          have hji : j ≠ i := by
            rintro rfl
            exact hmissing hjC
          refine mem_erase.mpr ⟨hji, ?_⟩
          by_cases hjx : x j = true
          · simp [trueDirections, hjx]
          · have hjfalse : x j = false := Bool.eq_false_of_not_eq_true hjx
            have hset : trueDirections (flip x j) = insert j (trueDirections x) := by
              ext k
              by_cases hk : k = j
              · subst k
                simp [trueDirections, hjfalse]
              · simp only [trueDirections, mem_filter, mem_univ, true_and, mem_insert, hk,
                  false_or]
                rw [BalancedCriticalSpectrum.flip, Function.update_of_ne hk]
            have hnot : j ∉ trueDirections x := by simp [trueDirections, hjfalse]
            have hu := hthin (flip x j) hjC (by
              simpa [BalancedCriticalSpectrum.flip, Ne.symm hji] using hxi)
            rw [hset, card_insert_of_notMem hnot, hcard] at hu
            omega
        have h := card_le_card hsub
        have hiX : i ∈ trueDirections x := by simp [trueDirections, hxi]
        rw [regular_directions C hr hxC, card_erase_of_mem hiX, hcard] at h
        omega
      simp [E, hflip, hxi, hxC]
    · intro x _ y _ h
      simpa using congrArg (flip · i) h
  have hsplit := card_sdiff_add_card_eq_card (filter_subset
    (fun x => (trueDirections x).card ≤ 2) H)
  change (H \ T).card + T.card = H.card at hsplit
  change H.card ≤ 9 + E.card
  omega

/-- The profile with eight deficits four and one deficit five cannot occur.
The true side of the last coordinate is confined to its first three layers. -/
private lemma no_four_eight_five_profile
    {C : Finset (Q 9)} (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hdir : directionEdges C 8 = 11)
    (hhalf : (C.filter (fun x => x 8 = true)).card = 23)
    (hweight : ∀ x ∈ C, (∑ j : Fin 9, if x j then (if j = 8 then (5 : ℤ) else 4) else 0) ≤ 16) :
    False := by
  have hthin (x : Q 9) (hx : x ∈ C) (hxi : x 8 = true) :
      (trueDirections x).card ≤ 3 := by
    have hi : (8 : Fin 9) ∈ trueDirections x := by simp [trueDirections, hxi]
    have hw := hweight x hx
    rw [← sum_filter] at hw
    change (∑ j ∈ trueDirections x, if j = 8 then (5 : ℤ) else 4) ≤ 16 at hw
    rw [← sum_erase_add _ _ hi, ite_eq_left rfl] at hw
    have hsum : (∑ j ∈ (trueDirections x).erase 8, if j = 8 then (5 : ℤ) else 4) =
        ((trueDirections x).erase 8).card * (4 : ℤ) := by
      rw [← nsmul_eq_mul, ← sum_const]
      apply sum_congr rfl
      intro j hj
      exact ite_eq_right (mem_erase.mp hj).1
    rw [hsum, card_erase_of_mem hi] at hw
    omega
  have h := thin_half_card_le hr 8 hthin
  omega

private def fourEightFiveProfile : List ℤ := List.ofFn (fun j : Fin 9 => if j = 8 then 5 else 4)

/-- A 66-point balanced cubic support has one of the 155 profiles left after
the suffix bounds and the radius-two obstruction in its last coordinate. -/
def sixtySixProfilesAfterThinHalf : List (List ℤ) :=
  sixtySixProfilesAfterSuffixBounds.filter (· != fourEightFiveProfile)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Reduce the profile filters in the kernel, including all coordinate intervals.
theorem sixtySixProfilesAfterThinHalf_length : sixtySixProfilesAfterThinHalf.length = 155 := by
  decide +kernel

/-- The remaining profiles include the normalized profile of any hypothetical
66-point Huang-balanced cubic support. -/
theorem q9_sixty_six_mem_profiles_after_thin_half {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterThinHalf := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_suffix_bounds hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterThinHalf, List.mem_filter]
  refine ⟨hprofile, ?_⟩
  have hne : List.ofFn r ≠ fourEightFiveProfile := by
    intro hp
    have he := List.ofFn_inj.mp hp
    subst r
    have hdir := direction_edge_count (d := 3) S hregS hbS 8
    have hslice := hhalf 8
    simp at hslice
    have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hS hregS hbS
    apply no_four_eight_five_profile hregS (by omega) (by omega)
    intro x hx
    have hw := coordinate_profile_weight_bound hS hregS hbS (fun _ => true) _ hhalf hx
    have hsum : (∑ j : Fin 9, if j = 8 then (5 : ℤ) else 4) = 37 := by decide +kernel
    have hcap : ((shell S x 7).card : ℤ) ≤ 8 := by
      exact_mod_cast sixty_six_distance_seven_le_eight hS hregS hbS hd hx
    rw [hsum] at hw
    omega
  exact bne_iff_ne.mpr hne

#print axioms sixtySixProfilesAfterThinHalf_length
#print axioms q9_sixty_six_mem_profiles_after_thin_half

/-- The integer indicator of a selected cube vertex. -/
def cubeMembership (C : Finset (Q 9)) (x : Q 9) : ℤ :=
  if x ∈ C then 1 else 0

/-- The integer indicator of a pair of selected cube vertices. -/
def cubePairMembership (C : Finset (Q 9)) (x y : Q 9) : ℤ :=
  cubeMembership C x * cubeMembership C y

private lemma sum_cube_membership (C : Finset (Q 9)) (A : Finset (Q 9)) :
    (∑ x ∈ A, cubeMembership C x) = ((A.filter (· ∈ C)).card : ℤ) := by
  simp only [cubeMembership, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]

/-- The lifted cubicity and distance-seven rows hold at every ambient vertex.
The membership factor makes the radius inequalities valid at exterior vertices. -/
theorem cube_lifted_incidence_rows {C : Finset (Q 9)} {r : Fin 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hshell : ∀ x ∈ C, (shell C x 7).card ≤ 8 ∧
      2 * (∑ i, if x i then r i else 0) + 12 ≤ (∑ i, r i) + (shell C x 7).card)
    (x : Q 9) :
    (∑ i : Fin 9, cubePairMembership C x (flip x i)) = 3 * cubeMembership C x ∧
    (2 * (∑ i, if x i then r i else 0) + 12 - ∑ i, r i) * cubeMembership C x ≤
      ∑ y ∈ univ.filter (fun y => hammingDist x y = 7), cubePairMembership C x y ∧
    (∑ y ∈ univ.filter (fun y => hammingDist x y = 7), cubePairMembership C x y) ≤
      8 * cubeMembership C x := by
  by_cases hx : x ∈ C
  · have hneighbor :
        (∑ i : Fin 9, cubeMembership C (flip x i)) = ((directions C x).card : ℤ) := by
      simp only [cubeMembership, directions, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have he :
        ((univ.filter (fun y => hammingDist x y = 7)).filter (· ∈ C)) = shell C x 7 := by
      ext y
      simp [shell, and_comm]
    have hs := sum_cube_membership C (univ.filter fun y => hammingDist x y = 7)
    rw [he] at hs
    have ⟨hcap, hweight⟩ := hshell x hx
    simp only [cubePairMembership, show cubeMembership C x = 1 by simp [cubeMembership, hx],
      one_mul, mul_one, hneighbor, regular_directions C hreg hx, Nat.cast_ofNat, hs, true_and]
    exact ⟨by omega, by exact_mod_cast hcap⟩
  · simp [cubePairMembership, cubeMembership, hx]

/-- A distance-seven pair and an incident edge in an agreement direction
cannot both contribute at the same selected root. -/
theorem cube_lifted_agreement_row {C : Finset (Q 9)}
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    {x y : Q 9} (hxy : hammingDist x y = 7) {i : Fin 9} (hi : x i = y i) :
    cubePairMembership C x y + cubePairMembership C x (flip x i) ≤ cubeMembership C x := by
  by_cases hx : x ∈ C
  · by_cases hy : y ∈ C
    · have hu := agreeing_coordinate_unused hd hy hxy hi
      have hf : flip x i ∉ C := fun h => (mem_sdiff.mp hu).2 ((mem_directions C x i).mpr h)
      simp [cubePairMembership, cubeMembership, hx, hy, hf]
    · by_cases hf : flip x i ∈ C <;> simp [cubePairMembership, cubeMembership, hx, hy, hf]
  · simp [cubePairMembership, cubeMembership, hx]

#print axioms cube_lifted_incidence_rows
#print axioms cube_lifted_agreement_row

private lemma sum_cube_membership_property (C : Finset (Q 9)) (P : Q 9 → Prop)
    [DecidablePred P] :
    (∑ x ∈ univ.filter P, cubeMembership C x) = ((C.filter P).card : ℤ) := by
  rw [sum_cube_membership]
  have he : (univ.filter P).filter (· ∈ C) = C.filter P := by
    ext x
    simp [and_comm]
  rw [he]

/-- Cardinalities of the support, parity classes, literal halves and
direction edges give the equality rows of the lifted system. -/
theorem cube_lifted_cardinality_rows {C : Finset (Q 9)} {r : Fin 9 → ℤ}
    (hC : C.card = 66)
    (hparity : ∀ b, (C.filter (fun x => cubeParity x = b)).card = 33)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33)
    (hedge : ∀ i, directionEdges C i = 11) :
    (∑ x : Q 9, cubeMembership C x) = 66 ∧
    (∀ b, (∑ x ∈ univ.filter (fun x => cubeParity x = b), cubeMembership C x) = 33) ∧
    (∀ i, (∑ x ∈ univ.filter (fun x => x i = true), cubeMembership C x) = 33 - 2 * r i) ∧
    ∀ i, (∑ x ∈ univ.filter (fun x => x i = false), cubePairMembership C x (flip x i)) = 11 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sum_cube_membership]
    have he : (univ : Finset (Q 9)).filter (· ∈ C) = C := by ext x; simp
    simp [he, hC]
  · intro b
    rw [sum_cube_membership_property C (fun x => cubeParity x = b), hparity b]
    rfl
  · intro i
    rw [sum_cube_membership_property C (fun x => x i = true)]
    linarith only [hhalf i]
  · intro i
    have hpoint (x : Q 9) : cubePairMembership C x (flip x i) =
        if x ∈ C ∧ flip x i ∈ C then 1 else 0 := by
      by_cases hx : x ∈ C <;> by_cases hy : flip x i ∈ C <;>
        simp [cubePairMembership, cubeMembership, hx, hy]
    have hfilter : ((univ.filter (fun x : Q 9 => x i = false)).filter
        (fun x => x ∈ C ∧ flip x i ∈ C)) =
        C.filter (fun x => x i = false ∧ flip x i ∈ C) := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      tauto
    simp_rw [hpoint]
    rw [← sum_filter, sum_const, hfilter]
    change (directionEdges C i : ℤ) • (1 : ℤ) = 11
    rw [zsmul_eq_mul, hedge i]
    rfl

/-- The membership and pair variables of an actual support satisfy the
three inequalities used to lift a two-vertex product. -/
theorem cube_lifted_pair_rows (C : Finset (Q 9)) (x y : Q 9) :
    cubePairMembership C x y ≤ cubeMembership C x ∧
    cubePairMembership C x y ≤ cubeMembership C y ∧
    cubeMembership C x + cubeMembership C y - cubePairMembership C x y ≤ 1 := by
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;>
    norm_num [cubePairMembership, cubeMembership, hx, hy]

/-- A forbidden pair contributes at most one vertex to the support. -/
theorem cube_lifted_forbidden_pair_row (C : Finset (Q 9)) (x y : Q 9)
    (h : x ∈ C → y ∉ C) :
    cubeMembership C x + cubeMembership C y ≤ 1 := by
  by_cases hx : x ∈ C
  · simp [cubeMembership, hx, h hx]
  · by_cases hy : y ∈ C <;> simp [cubeMembership, hx, hy]

/-- The original Huang signing gives a linear inequality on each cube square. -/
theorem cube_lifted_square_row {C : Finset (Q 9)} (hb : IsBalanced C) (x : Q 9)
    {i j : Fin 9} (hij : i ≠ j) :
    cubeMembership C x + cubeMembership C (flip x i) + cubeMembership C (flip x j) +
      cubeMembership C (flip (flip x i) j) ≤ 3 := by
  by_cases hx : x ∈ C <;> by_cases hi : flip x i ∈ C <;> by_cases hj : flip x j ∈ C
  all_goals
    first
    | have hf := BalancedCubeGirth.no_selected_square hb hij hx hi hj
      norm_num [cubeMembership, hx, hi, hj, hf]
    | by_cases hf : flip (flip x i) j ∈ C <;>
        norm_num [cubeMembership, hx, hi, hj, hf]

#print axioms cube_lifted_cardinality_rows
#print axioms cube_lifted_pair_rows
#print axioms cube_lifted_forbidden_pair_row
#print axioms cube_lifted_square_row

open private reindex reindex_regular reindex_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

/-- Transport a normalized support in the direction used by the orbit average.
The transported vertex indicators are exactly the precomposed indicators, and
the equations for the minority halves retain the same coordinate profile. -/
theorem transport_lifted_cube_support {C : Finset (Q 9)} {r : Fin 9 → ℤ}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33)
    (p : deficitPermutations r) :
    ∃ T : Finset (Q 9), T.card = 66 ∧
      ((hypercube 9).induce (T : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced T ∧
      (∀ i, ((T.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      ∀ x, cubeMembership T x = cubeMembership C (p • x) := by
  let e := reindex p.val.symm
  let T := C.image e
  have hcard : T.card = 66 := by
    simpa only [T, card_image_of_injective C e.injective] using hC
  refine ⟨T, hcard, reindex_regular hreg p.val.symm, reindex_balanced hb p.val.symm, ?_, ?_⟩
  · intro i
    have hfilter : T.filter (fun x => x i = true) =
        (C.filter (fun x => x (p.val i) = true)).image e := by
      ext x
      simp only [T, mem_filter, mem_image]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hbit⟩
        exact ⟨y, ⟨hy, hbit⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hbit⟩, rfl⟩
        exact ⟨⟨y, hy, rfl⟩, hbit⟩
    have hp : r (p.val i) = r i := p.property i
    rw [hfilter, card_image_of_injective _ e.injective, ← hp]
    exact hhalf (p.val i)
  · intro x
    have hx : x ∈ T ↔ e.symm x ∈ C := by
      constructor
      · intro h
        obtain ⟨y, hy, rfl⟩ := mem_image.mp h
        simpa only [Equiv.symm_apply_apply] using hy
      · intro h
        exact mem_image.mpr ⟨e.symm x, h, e.apply_symm_apply x⟩
    change (if x ∈ T then (1 : ℤ) else 0) =
      (if e.symm x ∈ C then (1 : ℤ) else 0)
    simp only [hx]

#print axioms transport_lifted_cube_support

end D5.S3.Combinatorics.Graph.HypercubeCritical
