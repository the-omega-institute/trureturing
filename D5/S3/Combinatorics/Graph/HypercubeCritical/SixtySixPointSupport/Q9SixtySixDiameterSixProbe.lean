/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterSixProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterSixProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every 66-vertex Huang-balanced induced cubic support of the nine-cube has a distance-seven pair. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixDistanceSumProbe

/-! The coordinate profile forced by the absence of distance-seven pairs. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyShellCompositionProbe
open private paritySide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

set_option maxHeartbeats 600000 in
-- The two coordinate-wise weight sums use both integer casts and support subtypes.
private lemma diameter_six_coordinate_profile {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 6) :
    ∃ (b : Fin 9 → Bool) (k : Fin 9),
      (∀ i, (C.filter (fun y => y i = b i)).card = if i = k then 33 else 21) ∧
      (∀ x ∈ C, (((univ : Finset (Fin 9)).erase k).filter (fun i => x i = b i)).card ≤ 3) := by
  have hcap (x : Q 9) (hx : x ∈ C) : (shell C x 7).card ≤ 0 := by
    apply Nat.le_zero.mpr
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hh := hd x hx y (mem_filter.mp hy).1
    rw [(mem_filter.mp hy).2] at hh
    omega
  obtain ⟨b,r,hrange,hr,hweight,hm⟩ := coordinate_profile_for_partner_cap hc hreg hb 0 hcap
  let S : ℤ := ∑ i, r i
  let P : ℤ := ∑ i, (r i)^2
  let delta (i : Fin 9) := 6 - r i
  have hSbound : S ≤ 54 := by
    have h := sum_le_sum (s := (univ : Finset (Fin 9))) (fun i _ => (hrange i).2)
    norm_num at h
    exact h
  have hPbound : P ≤ 6 * S := by
    dsimp only [P,S]
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    nlinarith [mul_nonneg (hrange i).1 (sub_nonneg.mpr (hrange i).2)]
  change 110 * S ≤ 198 * ((S - 12 + (0 : ℕ)) / 2) + 6 * P at hm
  have hSlow : 48 ≤ S := by omega
  have hdelta : (∑ i, delta i) = 54 - S := by
    simp [delta,S,sum_sub_distrib]
  let wt (x : Q 9) : ℕ := (univ.filter (fun i => x i = b i)).card
  let origin : Q 9 := fun i => !b i
  have ht (x : Q 9) : hammingDist origin x = wt x := by
    change ((univ : Finset (Fin 9)).filter (fun i => (!b i) ≠ x i)).card = _
    congr 1
    ext i
    simp only [mem_filter,mem_univ,true_and]
    cases b i <;> cases x i <;> decide
  have halldist : (∑ x ∈ C, (wt x : ℤ)) = 297 - 2 * S := by
    dsimp only [wt]
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [sum_comm,mul_sum]
    have hconst : (297 : ℤ) = ∑ _i : Fin 9, 33 := by norm_num
    rw [hconst,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    linarith [hr i]
  have hgeom (x : Q 9) (hx : x ∈ C) : 6 * (wt x : ℤ) ≤ (S - 12) / 2 + (54 - S) := by
    have hlocal : (6 * (wt x : ℤ)) ≤
         (∑ i : Fin 9, if x i = b i then r i else 0) + ∑ i, delta i := by
      dsimp only [wt]
      rw [card_filter,Nat.cast_sum,mul_sum,← sum_add_distrib]
      apply sum_le_sum
      intro i _
      push_cast
      by_cases h : x i = b i
      · simp [h,delta]
      · simp [h,delta,(hrange i).2]
    rw [hdelta] at hlocal
    have hw := hweight x hx
    change (∑ i : Fin 9, if x i = b i then r i else 0) ≤ (S - 12 + (0 : ℕ)) / 2 at hw
    omega
  have hS : S = 48 := by
    by_contra! hne
    have hw3 (x : Q 9) (hx : x ∈ C) : wt x ≤ 3 := by
      have hh := hgeom x hx
      omega
    have hp := sixty_six_parity_side_card hc hreg
    let E := C.filter (fun x => wt x % 2 = 0)
    have hE : E.card = 33 := by
      rw [← hp (cubeParity origin)]
      apply card_bij (fun x hx => (⟨x,(mem_filter.mp hx).1⟩ : (C : Set (Q 9))))
      · intro x hx
        have he := (mem_filter.mp hx).2
        rw [← ht x] at he
        exact mem_filter.mpr ⟨mem_univ _,((distance_parity origin x).mp he).symm⟩
      · intro x _ y _ h
        exact congrArg Subtype.val h
      · intro y hy
        have he := (distance_parity origin y.val).mpr (mem_filter.mp hy).2.symm
        rw [ht] at he
        exact ⟨y.val,mem_filter.mpr ⟨y.property,he⟩,rfl⟩
    have hsum := sum_le_sum (s := C) (f := fun x => (wt x : ℤ))
      (g := fun x => if wt x % 2 = 0 then 2 else 3) (fun x hx => by
        have hh := hw3 x hx
        split_ifs <;> omega)
    rw [sum_ite,sum_const,sum_const] at hsum
    have hn := card_filter_add_card_filter_not (s := C) (fun x => wt x % 2 = 0)
    change E.card + _ = C.card at hn
    rw [hE,hc] at hn
    have hO : (C.filter (fun x => ¬ wt x % 2 = 0)).card = 33 := by omega
    change (∑ x ∈ C, (wt x : ℤ)) ≤ E.card • (2 : ℤ) +
      (C.filter (fun x => ¬ wt x % 2 = 0)).card • (3 : ℤ) at hsum
    rw [halldist,hE,hO] at hsum
    norm_num at hsum
    omega
  have hdelta6 : (∑ i, delta i) = 6 := by omega
  have hP : P = 252 + ∑ i, (delta i)^2 := by
    have hi (i : Fin 9) : (r i)^2 = 36 - 12 * delta i + (delta i)^2 := by
      dsimp [delta]
      ring
    dsimp only [P]
    simp_rw [hi,sum_add_distrib,sum_sub_distrib,← mul_sum]
    norm_num [hdelta6]
  have hsq : 34 ≤ ∑ i, (delta i)^2 := by omega
  have hk : ∃ k, delta k = 6 := by
    by_contra! h
    have hle (i : Fin 9) : delta i ≤ 6 := by
      have hh := (hrange i).1
      dsimp [delta]
      omega
    have hsq' : (∑ i, (delta i)^2) ≤ 5 * ∑ i, delta i := by
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      have hnon : 0 ≤ delta i := by
        have hh := (hrange i).2
        dsimp [delta]
        omega
      have h5 : 0 ≤ 5 - delta i := by
        have hh := hle i
        have hn := h i
        omega
      nlinarith [mul_nonneg hnon h5]
    omega
  obtain ⟨k,hk⟩ := hk
  have hother (i : Fin 9) (hi : i ≠ k) : delta i = 0 := by
    have hnon (j : Fin 9) : 0 ≤ delta j := by
      have hh := (hrange j).2
      dsimp [delta]
      omega
    have hsum := sum_erase_add (univ : Finset (Fin 9)) delta (mem_univ k)
    rw [hdelta6,hk] at hsum
    have hi' : i ∈ (univ : Finset (Fin 9)).erase k := mem_erase.mpr ⟨hi,mem_univ _⟩
    have hb := single_le_sum (fun j _ => hnon j) hi'
    have hn := hnon i
    omega
  have hrk : r k = 0 := by dsimp [delta] at hk; omega
  have hri (i : Fin 9) (hi : i ≠ k) : r i = 6 := by
    have hh := hother i hi
    dsimp [delta] at hh
    omega
  refine ⟨b,k,?_,?_⟩
  · intro i
    have hh := hr i
    by_cases he : i = k
    · subst i
      rw [ite_eq_left rfl]
      omega
    · have hz := hri i he
      rw [ite_eq_right he]
      omega
  · intro x hx
    have hw := hweight x hx
    change (∑ i : Fin 9, if x i = b i then r i else 0) ≤ (S - 12 + (0 : ℕ)) / 2 at hw
    rw [← sum_erase_add (univ : Finset (Fin 9)) (fun i => if x i = b i then r i else 0)
        (mem_univ k),hrk] at hw
    have he : (∑ i ∈ (univ : Finset (Fin 9)).erase k, if x i = b i then r i else 0) =
        6 * ((((univ : Finset (Fin 9)).erase k).filter (fun i => x i = b i)).card : ℤ) := by
      rw [← sum_filter]
      calc
        _ = ∑ _i ∈ ((univ : Finset (Fin 9)).erase k).filter (fun i => x i = b i), (6 : ℤ) :=
          sum_congr rfl (fun i hi => hri i (mem_erase.mp (mem_filter.mp hi).1).1)
        _ = _ := by simp [mul_comm]
    rw [he] at hw
    split_ifs at hw <;> omega

#print axioms diameter_six_coordinate_profile

open BalancedCriticalSpectrum (directionEdges directionEndpoints direction_edge_count)
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

private def projectedWeight (b : Fin 9 → Bool) (k : Fin 9) (x : Q 9) : ℕ :=
  ((univ.erase k).filter (fun i => x i = b i)).card

private lemma projected_weight_flip (b : Fin 9 → Bool) (k i : Fin 9) (x : Q 9) :
    if i = k then projectedWeight b k (BalancedCriticalSpectrum.flip x i) = projectedWeight b k x
    else projectedWeight b k (BalancedCriticalSpectrum.flip x i) + 1 = projectedWeight b k x ∨
      projectedWeight b k (BalancedCriticalSpectrum.flip x i) = projectedWeight b k x + 1 := by
  unfold projectedWeight
  split_ifs with hi
  · congr 1
    ext j
    simp only [mem_filter,mem_erase,mem_univ,and_true]
    by_cases hj : j = k
    · simp [hj]
    · simp [BalancedCriticalSpectrum.flip,hi,hj]
  · let S := (univ.erase k : Finset (Fin 9))
    have hiS : i ∈ S := mem_erase.mpr ⟨hi,mem_univ _⟩
    have hfilter :
        (S.erase i).filter (fun j => BalancedCriticalSpectrum.flip x i j = b j) =
          (S.erase i).filter (fun j => x j = b j) := by
      ext j
      simp only [mem_filter,mem_erase]
      constructor <;> rintro ⟨⟨hne,hj⟩,hv⟩
      · exact ⟨⟨hne,hj⟩,by simpa [BalancedCriticalSpectrum.flip,hne] using hv⟩
      · exact ⟨⟨hne,hj⟩,by simpa [BalancedCriticalSpectrum.flip,hne] using hv⟩
    have hcard (f : Fin 9 → Prop) [DecidablePred f] :
        (S.filter f).card = ((S.erase i).filter f).card + if f i then 1 else 0 := by
      rw [← insert_erase hiS]
      have hs : (insert i (S.erase i)).filter f =
          if f i then insert i ((S.erase i).filter f) else (S.erase i).filter f := by
        ext j
        by_cases h : f i <;> simp [h] <;> grind
      rw [hs]
      split_ifs with h
      · rw [card_insert_of_notMem (fun hi' => (mem_erase.mp (mem_filter.mp hi').1).1 rfl)]
        simp
      · simp
    change (S.filter (fun j => BalancedCriticalSpectrum.flip x i j = b j)).card + 1 =
        (S.filter (fun j => x j = b j)).card ∨
      (S.filter (fun j => BalancedCriticalSpectrum.flip x i j = b j)).card =
        (S.filter (fun j => x j = b j)).card + 1
    rw [hcard,hcard,hfilter,BalancedCriticalSpectrum.flip_apply_same]
    cases x i <;> cases b i <;> simp <;> omega

private lemma projected_weight_total {C : Finset (Q 9)} (b : Fin 9 → Bool) (k : Fin 9)
    (h : ∀ i, (C.filter (fun y => y i = b i)).card = if i = k then 33 else 21) :
    (∑ x ∈ C, projectedWeight b k x) = 168 := by
  unfold projectedWeight
  simp only [card_filter]
  rw [sum_comm]
  simp_rw [← card_filter, h]
  have he : (∑ i ∈ (univ : Finset (Fin 9)).erase k, if i = k then 33 else 21) =
      ∑ _i ∈ (univ : Finset (Fin 9)).erase k, 21 := by
    apply sum_congr rfl
    intro i hi
    rw [ite_eq_right (mem_erase.mp hi).1]
  rw [he,sum_const,card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin]
  decide

open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
  (directions regular_directions)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

private lemma projected_weight_slack
    {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (b : Fin 9 → Bool) (k : Fin 9)
    (hparts : ∀ i, (C.filter (fun y => y i = b i)).card = if i = k then 33 else 21)
    (hmax : ∀ x ∈ C, projectedWeight b k x ≤ 3) :
    let g (x : Q 9) : ℤ := 3 - projectedWeight b k x
    let threshold (i : Fin 9) : ℤ := if i = k then 0 else 1
    (∑ i : Fin 9, ∑ x ∈ directionEndpoints C i,
      (g x + g (BalancedCriticalSpectrum.flip x i) - threshold i)) = 4 ∧
      ∀ i, ∀ x ∈ directionEndpoints C i,
        0 ≤ g x + g (BalancedCriticalSpectrum.flip x i) - threshold i := by
  let g (x : Q 9) : ℤ := 3 - projectedWeight b k x
  let threshold (i : Fin 9) : ℤ := if i = k then 0 else 1
  have hsum : (∑ x ∈ C, g x) = 30 := by
    dsimp only [g]
    rw [sum_sub_distrib,sum_const,hc,nsmul_eq_mul,← Nat.cast_sum,projected_weight_total b k hparts]
    norm_num
  have hT : ∑ i : Fin 9, threshold i = 8 := by
    rw [← sum_erase_add univ threshold (mem_univ k)]
    have he : (∑ i ∈ (univ : Finset (Fin 9)).erase k, threshold i) =
        ∑ _i ∈ (univ : Finset (Fin 9)).erase k, (1 : ℤ) := by
      apply sum_congr rfl
      intro i hi
      simp [threshold,(mem_erase.mp hi).1]
    rw [he,sum_const,card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin]
    norm_num [threshold]
  have hdir (i : Fin 9) : (directionEndpoints C i).card = 22 := by
    have h := direction_edge_count (d := 3) C hreg hb i
    rw [endpoint_card_twice]
    omega
  constructor
  · change (∑ i : Fin 9, ∑ x ∈ directionEndpoints C i,
      (g x + g (BalancedCriticalSpectrum.flip x i) - threshold i)) = 4
    simp_rw [sum_sub_distrib,sum_add_distrib,endpoint_weight_swap C _ g,sum_const,hdir,nsmul_eq_mul]
    rw [← mul_sum,endpoint_weight_sum C hreg,hsum,hT]
    norm_num
  · intro i x hx
    have hxC := (mem_filter.mp hx).1
    have hflip := (mem_filter.mp hx).2
    have h1 := hmax x hxC
    have h2 := hmax (BalancedCriticalSpectrum.flip x i) hflip
    have hstep := projected_weight_flip b k i x
    change 0 ≤ g x + g (BalancedCriticalSpectrum.flip x i) - threshold i
    dsimp only [g,threshold]
    by_cases hi : i = k
    · rw [ite_eq_left hi]
      omega
    · rw [ite_eq_right hi] at hstep ⊢
      rcases hstep with h | h <;> omega

#print axioms projected_weight_slack

set_option maxHeartbeats 600000 in
-- Endpoint weights are compared in two orders of summation.
private lemma projected_layer_counts
    {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (b : Fin 9 → Bool) (k : Fin 9)
    (hparts : ∀ i, (C.filter (fun y => y i = b i)).card = if i = k then 33 else 21)
    (hmax : ∀ x ∈ C, projectedWeight b k x ≤ 3) :
    (C.filter (fun x => projectedWeight b k x = 2)).card = 30 ∧
    ((directionEndpoints C k).filter (fun x => projectedWeight b k x = 2)).card ≤ 2 := by
  let wt := projectedWeight b k
  let g (x : Q 9) : ℤ := 3 - wt x
  let t (i : Fin 9) : ℤ := if i = k then 0 else 1
  let q (i : Fin 9) (x : Q 9) := g x + g (BalancedCriticalSpectrum.flip x i) - t i
  obtain ⟨hslack,hnon⟩ := projected_weight_slack hc hreg hb b k hparts hmax
  change (∑ i : Fin 9, ∑ x ∈ directionEndpoints C i, q i x) = 4 at hslack
  change ∀ i, ∀ x ∈ directionEndpoints C i, 0 ≤ q i x at hnon
  have hlow (x : Q 9) (hx : x ∈ C) : 2 ≤ wt x := by
    by_contra! hsmall
    have hq (i : Fin 9) (hi : i ∈ directions C x) : 2 ≤ q i x := by
      have hstep := projected_weight_flip b k i x
      by_cases he : i = k
      · rw [ite_eq_left he] at hstep
        have h : wt (BalancedCriticalSpectrum.flip x i) = wt x := hstep
        dsimp only [q,g,t]
        rw [ite_eq_left he,h]
        omega
      · rw [ite_eq_right he] at hstep
        change wt (BalancedCriticalSpectrum.flip x i) + 1 = wt x ∨
          wt (BalancedCriticalSpectrum.flip x i) = wt x + 1 at hstep
        dsimp only [q,g,t]
        rw [ite_eq_right he]
        omega
    have hpoint (i : Fin 9) :
        (if i ∈ directions C x then q i x else 0) ≤ ∑ y ∈ directionEndpoints C i, q i y := by
      by_cases hi : i ∈ directions C x
      · rw [ite_eq_left hi]
        have hflip := (mem_directions C x i).mp hi
        exact single_le_sum (hnon i) (mem_filter.mpr ⟨hx,hflip⟩)
      · rw [ite_eq_right hi]
        exact sum_nonneg (hnon i)
    have htotal := sum_le_sum (s := (univ : Finset (Fin 9))) (fun i _ => hpoint i)
    rw [hslack,← sum_filter] at htotal
    have he : (univ : Finset (Fin 9)).filter (fun i => i ∈ directions C x) = directions C x := by
      ext i
      simp
    rw [he] at htotal
    have h6 := sum_le_sum (s := directions C x) hq
    rw [sum_const,regular_directions C hreg hx] at h6
    norm_num at h6
    omega
  have hcard : (C.filter (fun x => wt x = 2)).card = 30 := by
    have htotal := projected_weight_total b k hparts
    change (∑ x ∈ C, wt x) = 168 at htotal
    have hwt x (hx : x ∈ C) : wt x = if wt x = 2 then 2 else 3 := by
      have h₁ := hlow x hx
      have h₂ : wt x ≤ 3 := hmax x hx
      split_ifs <;> omega
    rw [sum_congr rfl hwt, sum_ite, sum_const, sum_const] at htotal
    have hpart := card_filter_add_card_filter_not (s := C) (fun x => wt x = 2)
    rw [hc] at hpart
    simp only [smul_eq_mul] at htotal
    omega
  refine ⟨hcard,?_⟩
  let M := (directionEndpoints C k).filter (fun x => wt x = 2)
  have hm (x : Q 9) (hx : x ∈ M) : q k x = 2 := by
    have hxw := (mem_filter.mp hx).2
    have he := projected_weight_flip b k k x
    rw [ite_eq_left rfl] at he
    change wt (BalancedCriticalSpectrum.flip x k) = wt x at he
    dsimp only [q,g,t]
    rw [ite_eq_left rfl,he,hxw]
    norm_num
  have hsmall :=
    sum_le_sum_of_subset_of_nonneg (f := q k) (s := M) (t := directionEndpoints C k)
      (filter_subset _ _) (fun x hx _ => hnon k x hx)
  rw [sum_congr rfl hm,sum_const,nsmul_eq_mul] at hsmall
  have hk := single_le_sum
    (f := fun i => ∑ x ∈ directionEndpoints C i, q i x)
    (fun i _ => sum_nonneg (hnon i)) (mem_univ k)
  rw [hslack] at hk
  change M.card ≤ 2
  omega

#print axioms projected_layer_counts

private lemma projected_two_layer_bound {C : Finset (Q 9)} (b : Fin 9 → Bool) (k : Fin 9)
    (hpaired : ((directionEndpoints C k).filter (fun x => projectedWeight b k x = 2)).card ≤ 2) :
    (C.filter (fun x => projectedWeight b k x = 2)).card ≤ 29 := by
  let project (x : Q 9) : Finset (Fin 9) :=
    (univ.erase k).filter (fun i => x i = b i)
  let L := C.filter (fun x => projectedWeight b k x = 2)
  let Z := L.filter (fun x => x k = false)
  let O := L.filter (fun x => x k = true)
  let A := Z.image project
  let B := O.image project
  let P := (univ.erase k : Finset (Fin 9)).powersetCard 2
  have eq_away {x y : Q 9} (he : project x = project y) {i : Fin 9} (hi : i ≠ k) :
      x i = y i := by
    have h : x i = b i ↔ y i = b i := by
      have hm : i ∈ project x ↔ i ∈ project y := he ▸ Iff.rfl
      simpa [project,hi] using hm
    cases hx : x i <;> cases hy : y i <;> cases hb : b i <;> simp [hx,hy,hb] at h ⊢
  have inj (t : Bool) : Set.InjOn project ((L.filter (fun x => x k = t)) : Set (Q 9)) := by
    intro x hx y hy he
    funext i
    by_cases hi : i = k
    · subst i
      exact ((mem_filter.mp hx).2).trans (mem_filter.mp hy).2.symm
    · exact eq_away he hi
  have hZ : A.card = Z.card := card_image_of_injOn (inj false)
  have hO : B.card = O.card := card_image_of_injOn (inj true)
  have hsum : Z.card + O.card = L.card := by
    have h := card_filter_add_card_filter_not (s := L) (fun x => x k = false)
    have he : L.filter (fun x => ¬x k = false) = O := by
      ext x
      cases x k <;> simp [O]
    rw [he] at h
    exact h
  have img_subset (F : Finset (Q 9)) (hF : F ⊆ L) : F.image project ⊆ P := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    exact mem_powersetCard.mpr ⟨filter_subset _ _,(mem_filter.mp (hF hx)).2⟩
  have hP : P.card = 28 := by
    rw [show P = (univ.erase k : Finset (Fin 9)).powersetCard 2 from rfl,
      card_powersetCard,card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin]
    decide
  have hunion : (A ∪ B).card ≤ 28 :=
    (card_le_card (union_subset (img_subset Z (filter_subset _ _))
      (img_subset O (filter_subset _ _)))).trans_eq hP
  let Z' := Z.filter (fun x => project x ∈ B)
  let O' := O.filter (fun x => project x ∈ A)
  have hZ' : Z'.image project = A ∩ B := by
    ext p
    simp only [Z',A,mem_image,mem_filter,mem_inter]
    constructor
    · rintro ⟨x,⟨hx,hxp⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,hxp⟩
    · rintro ⟨⟨x,hx,rfl⟩,hp⟩
      exact ⟨x,⟨hx,hp⟩,rfl⟩
  have hO' : O'.image project = A ∩ B := by
    ext p
    simp only [O',B,mem_image,mem_filter,mem_inter]
    constructor
    · rintro ⟨x,⟨hx,hxp⟩,rfl⟩
      exact ⟨hxp,⟨x,hx,rfl⟩⟩
    · rintro ⟨hp,⟨x,hx,rfl⟩⟩
      exact ⟨x,⟨hx,hp⟩,rfl⟩
  have hkflip {x y : Q 9} (he : project x = project y) (hxy : x k ≠ y k) :
      y = BalancedCriticalSpectrum.flip x k := by
    funext i
    by_cases hi : i = k
    · subst i
      rw [BalancedCriticalSpectrum.flip_apply_same]
      exact Bool.eq_not_of_ne hxy.symm
    · simpa [BalancedCriticalSpectrum.flip,hi] using (eq_away he hi).symm
  have hsub : Z' ∪ O' ⊆ (directionEndpoints C k).filter (fun x => projectedWeight b k x = 2) := by
    intro x hx
    rcases mem_union.mp hx with hz | ho
    · obtain ⟨hZ,hB⟩ := mem_filter.mp hz
      obtain ⟨y,hy,he⟩ := mem_image.mp hB
      have hx0 := (mem_filter.mp hZ).2
      have hy1 := (mem_filter.mp hy).2
      have hxy : x k ≠ y k := by rw [hx0,hy1]; decide
      have h := hkflip he.symm hxy
      obtain ⟨hxC,hxw⟩ := mem_filter.mp (mem_filter.mp hZ).1
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hxC,h ▸ (mem_filter.mp (mem_filter.mp hy).1).1⟩,hxw⟩
    · obtain ⟨hO,hA⟩ := mem_filter.mp ho
      obtain ⟨y,hy,he⟩ := mem_image.mp hA
      have hx1 := (mem_filter.mp hO).2
      have hy0 := (mem_filter.mp hy).2
      have hxy : x k ≠ y k := by rw [hx1,hy0]; decide
      have h := hkflip he.symm hxy
      obtain ⟨hxC,hxw⟩ := mem_filter.mp (mem_filter.mp hO).1
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hxC,h ▸ (mem_filter.mp (mem_filter.mp hy).1).1⟩,hxw⟩
  have hdis : Disjoint Z' O' := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have he := ((mem_filter.mp (mem_filter.mp hx).1).2).symm.trans
      (mem_filter.mp (mem_filter.mp hy).1).2
    contradiction
  have hle := (card_le_card hsub).trans hpaired
  rw [card_union_of_disjoint hdis] at hle
  have hzle : (A ∩ B).card ≤ Z'.card := by rw [← hZ']; exact card_image_le
  have hole : (A ∩ B).card ≤ O'.card := by rw [← hO']; exact card_image_le
  have h := card_union_add_card_inter A B
  change L.card ≤ 29
  omega

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- A 66-vertex Huang-balanced induced cubic support in the nine-cube has diameter seven. -/
theorem huang_balanced_cubic_sixty_six_exists_distance_seven {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ x ∈ C, ∃ y ∈ C, hammingDist x y = 7 := by
  by_contra! h
  have hd (x : Q 9) (hx : x ∈ C) (y : Q 9) (hy : y ∈ C) : hammingDist x y ≤ 6 := by
    have hle := huang_balanced_cubic_sixty_six_diameter_le_seven hc hreg hb x hx y hy
    have hne := h x hx y hy
    omega
  obtain ⟨b,k,hparts,hmax⟩ := diameter_six_coordinate_profile hc hreg hb hd
  obtain ⟨hcard,hpaired⟩ := projected_layer_counts hc hreg hb b k hparts hmax
  have hle := projected_two_layer_bound b k hpaired
  omega

#print axioms huang_balanced_cubic_sixty_six_exists_distance_seven

end D5.S3.Combinatorics.Graph.HypercubeCritical
