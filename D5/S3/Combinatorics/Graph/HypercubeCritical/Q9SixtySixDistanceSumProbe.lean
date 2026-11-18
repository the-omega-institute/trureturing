import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDiameterProbe
import Mathlib.Data.Fin.Tuple.Sort

/-! The one-point distance sum that constrains the 66-vertex coordinate profiles. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private second third second_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private root_data from D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private paritySide parity_bipartite parity_union from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private second_distance third_distance distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private balanced_cubic_hamming_two_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9FourthLeafSignProbe

set_option maxHeartbeats 550000 in
-- The degree, parity and distance filters involve the induced support subtype.
private lemma sixty_six_distance_sum_bound {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    {x : Q 9} (hx : x ∈ C) :
    (∑ y ∈ C, hammingDist x y) ≤ 273 + 2 * (shell C x 7).card := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let r : (C : Set (Q 9)) := ⟨x,hx⟩
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hc hr hb
  have hp (b : Bool) : (paritySide C b).card = 33 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite C)
    simp only [hr.degree_eq,Finset.sum_const,smul_eq_mul] at hs
    have hu := congrArg Finset.card (parity_union C)
    rw [Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact Bool.false_ne_true ((mem_filter.mp hz).2.symm.trans (mem_filter.mp hz').2)),
      card_univ,show Fintype.card (C : Set (Q 9)) = 66 by simpa using hc] at hu
    cases b <;> omega
  have hshell (k : ℕ) : (shell C x k).card =
      ((univ : Finset (C : Set (Q 9))).filter (fun y => hammingDist x y.val = k)).card := by
    apply card_bij (fun y hy => (⟨y,(mem_filter.mp hy).1⟩ : (C : Set (Q 9))))
    · intro y hy
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
    · intro _ _ _ _ h
      exact congrArg Subtype.val h
    · intro y hy
      exact ⟨y.val,mem_filter.mpr ⟨y.property,(mem_filter.mp hy).2⟩,rfl⟩
  have hn1 : (shell C x 1).card = 3 := by
    rw [hshell]
    have h : (univ.filter (fun y : (C : Set (Q 9)) => hammingDist x y.val = 1)) =
        G.neighborFinset r := by
      ext y
      simp only [mem_filter,mem_univ,true_and,G.mem_neighborFinset]
      rfl
    rw [h,G.card_neighborFinset_eq_degree]
    exact hr.degree_eq r
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  have hn2 : 6 ≤ (shell C x 2).card := by
    rw [hshell,← second_card hg (hr.degree_eq r) (fun y _ => hr.degree_eq y)]
    exact card_le_card (fun y hy => mem_filter.mpr ⟨mem_univ _,second_distance hy⟩)
  have hn3 : 12 ≤ (shell C x 3).card := by
    rw [hshell,← (root_data (parity_bipartite C) hg hr.degree_eq r).2.1]
    exact card_le_card (fun y hy => mem_filter.mpr ⟨mem_univ _,third_distance hy⟩)
  have hn24 : 18 ≤ (shell C x 2).card + (shell C x 4).card := by
    rw [hshell,hshell]
    exact balanced_cubic_hamming_two_four hr hb r
  have hn0 : 1 ≤ (shell C x 0).card :=
    card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,hammingDist_self x⟩⟩
  have hsum (f : ℕ → ℕ) : (∑ k ∈ range 8, (shell C x k).card * f k) =
      ∑ y ∈ C, f (hammingDist x y) := by
    simpa only [shell,Finset.sum_const,smul_eq_mul] using
      sum_fiberwise_of_maps_to' (s := C) (t := range 8) (g := hammingDist x)
        (fun y hy => mem_range.mpr (Nat.lt_succ_of_le (hd x hx y hy))) f
  have heven : (∑ y ∈ C, if hammingDist x y % 2 = 0 then 1 else 0) = 33 := by
    rw [← card_filter]
    trans (paritySide C (cubeParity x)).card
    · apply card_bij (fun y hy => (⟨y,(mem_filter.mp hy).1⟩ : (C : Set (Q 9))))
      · intro y hy
        exact mem_filter.mpr ⟨mem_univ _,((distance_parity x y).mp (mem_filter.mp hy).2).symm⟩
      · intro _ _ _ _ h
        exact congrArg Subtype.val h
      · intro y hy
        exact ⟨y.val,mem_filter.mpr ⟨y.property,
          (distance_parity x y.val).mpr (mem_filter.mp hy).2.symm⟩,rfl⟩
    · exact hp _
  have hall := hsum (fun _ => 1)
  have he := (hsum (fun k => if k % 2 = 0 then 1 else 0)).trans heven
  have hdSum := hsum id
  simp only [sum_range_succ,sum_range_zero,Nat.reduceMod,ite_true,Nat.mul_one,Nat.mul_zero,
    Nat.zero_add,Nat.add_zero,id_eq] at hall he hdSum
  simp only [Finset.sum_const,smul_eq_mul,Nat.mul_one,hc] at hall
  omega

#print axioms sixty_six_distance_sum_bound

private lemma distance_sum_by_coordinate (C : Finset (Q 9)) (x : Q 9) :
    (∑ y ∈ C, hammingDist x y) =
      ∑ i : Fin 9, (C.filter (fun y => y i ≠ x i)).card := by
  have hd (y : Q 9) : hammingDist x y = ∑ i : Fin 9, if y i ≠ x i then 1 else 0 := by
    rw [hammingDist_comm]
    exact card_filter _ _
  simp_rw [hd]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  exact (card_filter _ _).symm

/-- Orient the bits towards the chosen coordinate halves. Their deficits from 33
give the exact distance sum as a weighted Hamming weight. -/
private lemma coordinate_profile_distance (C : Finset (Q 9)) (hc : C.card = 66)
    (b : Fin 9 → Bool) (r : Fin 9 → ℤ)
    (hr : ∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33)
    (x : Q 9) :
    ((∑ y ∈ C, hammingDist x y) : ℤ) + 2 * (∑ i, r i) =
      297 + 4 * ∑ i : Fin 9, if x i = b i then r i else 0 := by
  have hdist := congrArg (fun n : ℕ => (n : ℤ)) (distance_sum_by_coordinate C x)
  push_cast at hdist
  rw [hdist,mul_sum,← sum_add_distrib]
  have hterm (i : Fin 9) :
      ((C.filter fun y => y i ≠ x i).card : ℤ) + 2 * r i =
        33 + 4 * (if x i = b i then r i else 0) := by
    by_cases he : x i = b i
    · rw [ite_eq_left he,he]
      have hs := card_filter_add_card_filter_not (s := C) (fun y => y i = b i)
      rw [hc] at hs
      have hs' : ((C.filter (fun y => y i = b i)).card : ℤ) +
          ((C.filter (fun y => y i ≠ b i)).card : ℤ) = 66 := by exact_mod_cast hs
      linarith [hr i]
    · rw [ite_eq_right he]
      have hf : (C.filter fun y => y i ≠ x i) = C.filter (fun y => y i = b i) := by
        ext y
        have ht := Bool.eq_not_of_ne he
        simp only [ht,mem_filter]
        cases b i <;> cases y i <;> simp
      rw [hf]
      simpa using hr i
  simp_rw [hterm,sum_add_distrib,← mul_sum]
  norm_num

private lemma coordinate_profile_weight_bound {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (b : Fin 9 → Bool) (r : Fin 9 → ℤ)
    (hr : ∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33)
    {x : Q 9} (hx : x ∈ C) :
    2 * (∑ i : Fin 9, if x i = b i then r i else 0) + 12 ≤
      (∑ i, r i) + (shell C x 7).card := by
  have hm := coordinate_profile_distance C hc b r hr x
  have hd := sixty_six_distance_sum_bound hc hreg hb hx
  have hdi : ((∑ y ∈ C, hammingDist x y) : ℤ) ≤ 273 + 2 * ((shell C x 7).card : ℤ) := by
    exact_mod_cast hd
  linarith

#print axioms coordinate_profile_weight_bound

open BalancedCriticalSpectrum (directionEndpoints directionEdges direction_edge_count)
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private directions mem_directions regular_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

private lemma endpoint_weight_sum (C : Finset (Q 9))
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (g : Q 9 → ℤ) :
    (∑ i : Fin 9, ∑ x ∈ directionEndpoints C i, g x) = 3 * ∑ x ∈ C, g x := by
  simp only [directionEndpoints,sum_filter]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [← sum_filter]
  change (∑ _i ∈ directions C x, g x) = 3 * g x
  rw [sum_const,regular_directions C hreg hx,nsmul_eq_mul]
  norm_num

private lemma endpoint_weight_swap (C : Finset (Q 9)) (i : Fin 9) (g : Q 9 → ℤ) :
    (∑ x ∈ directionEndpoints C i, g (BalancedCriticalSpectrum.flip x i)) =
      ∑ x ∈ directionEndpoints C i, g x := by
  apply sum_bij (fun x _ => BalancedCriticalSpectrum.flip x i)
  · intro x hx
    obtain ⟨hxc,hf⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hf,by simpa using hxc⟩
  · intro x _ y _ he
    simpa using congrArg (fun z => BalancedCriticalSpectrum.flip z i) he
  · intro y hy
    obtain ⟨hyc,hf⟩ := mem_filter.mp hy
    exact ⟨BalancedCriticalSpectrum.flip y i,mem_filter.mpr ⟨hf,by simpa using hyc⟩,by simp⟩
  · intro x hx
    rfl

private lemma sixty_six_edge_weight_inequality {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (r : Fin 9 → ℤ) (g : Q 9 → ℤ)
    (hgap : ∀ i, ∀ x ∈ directionEndpoints C i, r i ≤ g x + g (BalancedCriticalSpectrum.flip x i)) :
    11 * (∑ i, r i) ≤ 3 * ∑ x ∈ C, g x := by
  have hdirs (i : Fin 9) : (directionEndpoints C i).card = 22 := by
    have h := direction_edge_count (d := 3) C hreg hb i
    rw [endpoint_card_twice]
    omega
  have hdir (i : Fin 9) : 11 * r i ≤ ∑ x ∈ directionEndpoints C i, g x := by
    have h := sum_le_sum (s := directionEndpoints C i) (hgap i)
    rw [sum_add_distrib,endpoint_weight_swap,sum_const,hdirs,nsmul_eq_mul] at h
    norm_num at h
    linarith
  have h := sum_le_sum (s := (univ : Finset (Fin 9))) (fun i _ => hdir i)
  rw [← mul_sum,endpoint_weight_sum C hreg] at h
  exact h

private lemma coordinate_profile_moment_bound {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (b : Fin 9 → Bool) (r : Fin 9 → ℤ) (K : ℤ)
    (hr : ∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33)
    (hK : ∀ x ∈ C, (∑ i : Fin 9, if x i = b i then r i else 0) ≤ K) :
    110 * (∑ i, r i) ≤ 198 * K + 6 * (∑ i, (r i)^2) := by
  let w (x : Q 9) : ℤ := ∑ i : Fin 9, if x i = b i then r i else 0
  let g (x : Q 9) : ℤ := K - w x
  have hgn (x : Q 9) (hx : x ∈ C) : 0 ≤ g x := sub_nonneg.mpr (hK x hx)
  have hlocal (i : Fin 9) (x : Q 9) (hx : x ∈ directionEndpoints C i) :
      r i ≤ g x + g (BalancedCriticalSpectrum.flip x i) := by
    have hxC := (mem_filter.mp hx).1
    have hflipC := (mem_filter.mp hx).2
    let f (x : Q 9) (j : Fin 9) : ℤ := if x j = b j then r j else 0
    have hsplit (y : Q 9) :
        w y = f y i + ∑ j ∈ (univ : Finset (Fin 9)).erase i, f y j := by
      exact (sum_erase_add _ _ (mem_univ i)).symm.trans (add_comm _ _)
    have he : (∑ j ∈ (univ : Finset (Fin 9)).erase i, f x j) =
        ∑ j ∈ (univ : Finset (Fin 9)).erase i, f (BalancedCriticalSpectrum.flip x i) j := by
      apply sum_congr rfl
      intro j hj
      simp [f,BalancedCriticalSpectrum.flip,(mem_erase.mp hj).1]
    have hn : 0 ≤ g x := hgn x hxC
    have hn' : 0 ≤ g (BalancedCriticalSpectrum.flip x i) := hgn _ hflipC
    have he' (y : Q 9) : g y = K - (f y i + ∑ j ∈ (univ : Finset (Fin 9)).erase i, f y j) :=
      congrArg (K - ·) (hsplit y)
    rw [he' x,he] at hn
    rw [he' x,he' (BalancedCriticalSpectrum.flip x i),he]
    rw [he' (BalancedCriticalSpectrum.flip x i)] at hn'
    simp only [f,BalancedCriticalSpectrum.flip_apply_same] at hn hn' ⊢
    cases hi : x i <;> cases hj : b i <;> simp [hi,hj] at hn hn' ⊢ <;> linarith
  have hedge := sixty_six_edge_weight_inequality hc hreg hb r g hlocal
  have hw : (∑ x ∈ C, w x) = 33 * (∑ i, r i) - 2 * (∑ i, (r i)^2) := by
    dsimp only [w]
    rw [sum_comm,mul_sum,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    nlinarith [congrArg (· * r i) (hr i)]
  have hs : (∑ x ∈ C, g x) = 66 * K - (33 * (∑ i, r i) - 2 * (∑ i, (r i)^2)) := by
    dsimp only [g]
    rw [sum_sub_distrib,sum_const,hc,nsmul_eq_mul,hw]
    norm_num
  rw [hs] at hedge
  linarith

#print axioms coordinate_profile_moment_bound

open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open private reindex reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private balanced_subset coordinate_slice_degree_cases coordinate_slice_low_independent
  low_slice_card_eq_q parts_card sum_degrees_parts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private sixty_six_half_card_ge_twenty_one from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe

private lemma sixty_six_odd_coordinate_half {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (i : Fin 9) (b : Bool) : (C.filter (fun x => x i = b)).card % 2 = 1 := by
  let p := Equiv.swap i (0 : Fin 9)
  let T := C.image (reindex p)
  let S := coordinateSlice T b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hreg' := reindex_regular hreg p
  have hb' := reindex_balanced hb p
  have ht : T.card = 66 := by
    simpa [T,card_image_of_injective _ (reindex p).injective] using hc
  have hsize : S.card = (C.filter (fun x => x i = b)).card := by
    dsimp [S,T,p]
    rw [reindex_slice,card_image_of_injective _ (reindex _).injective]
  have hd : ∀ v, G.degree v = 2 ∨ G.degree v = 3 :=
    fun v => coordinate_slice_degree_cases v.property hreg'
  have hdir : 6 * directionEdges T 0 = 66 := by
    simpa [ht] using direction_edge_count (d := 3) T hreg' hb' 0
  have htwo := low_slice_card_eq_q (b := b) hreg'
  change (degreeTwo G univ).card = directionEdges T 0 at htwo
  have hcard := parts_card G hd univ
  rw [card_univ,show Fintype.card (S : Set (Q 9)) = S.card by simp] at hcard
  have hsum : 2 * (degreeTwo G univ).card + 3 * (degreeThree G univ).card =
      2 * G.edgeFinset.card := by
    rw [← sum_degrees_parts G hd univ]
    exact G.sum_degrees_eq_twice_card_edges
  omega

/-- The high vertices of a twenty-one-point slice split as two and eight or four and six. -/
private lemma twenty_one_high_parity_split (S : Finset (Q 9)) (hS : S.card = 21)
    (hdeg : ∀ v, ((hypercube 9).induce (S : Set (Q 9))).degree v = 2 ∨
      ((hypercube 9).induce (S : Set (Q 9))).degree v = 3)
    (hcount : (degreeTwo ((hypercube 9).induce (S : Set (Q 9))) univ).card = 11) :
    ∃ b : Bool,
      let G := (hypercube 9).induce (S : Set (Q 9))
      let L := paritySide S b
      let R := paritySide S (!b)
      ((degreeThree G L).card = 2 ∧ (degreeThree G R).card = 8) ∨
        ((degreeThree G L).card = 4 ∧ (degreeThree G R).card = 6) := by
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hp : G.IsBipartiteWith (L : Set (S : Set (Q 9))) (R : Set (S : Set (Q 9))) :=
    parity_bipartite S
  have hd : Disjoint L R := by simpa only [Finset.disjoint_coe] using hp.disjoint
  have hu : L ∪ R = univ := parity_union S
  have hab : L.card + R.card = 21 := by
    rw [← card_union_of_disjoint hd, hu, card_univ]
    simpa using hS
  have hd₂ : Disjoint (degreeTwo G L) (degreeTwo G R) :=
    hd.mono (filter_subset _ _) (filter_subset _ _)
  have hu₂ : degreeTwo G L ∪ degreeTwo G R = degreeTwo G univ := by
    simp only [degreeTwo, ← filter_union, hu]
  have hlows : (degreeTwo G L).card + (degreeTwo G R).card = 11 := by
    rw [← card_union_of_disjoint hd₂, hu₂, hcount]
  have hsum : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card := by
    calc
      _ = ∑ v ∈ L, G.degree v := (sum_degrees_parts G hdeg L).symm
      _ = ∑ v ∈ R, G.degree v := SimpleGraph.isBipartiteWith_sum_degrees_eq hp
      _ = _ := sum_degrees_parts G hdeg R
  have hL := parts_card G hdeg L
  have hR := parts_card G hdeg R
  have htotal : (degreeThree G L).card + (degreeThree G R).card = 10 := by omega
  have hsplit : (degreeThree G L).card = 2 ∨ (degreeThree G L).card = 4 ∨
      (degreeThree G L).card = 6 ∨ (degreeThree G L).card = 8 := by omega
  rcases hsplit with h | h | h | h
  · have hR8 : (degreeThree G R).card = 8 := by omega
    exact ⟨false, Or.inl ⟨h, hR8⟩⟩
  · have hR6 : (degreeThree G R).card = 6 := by omega
    exact ⟨false, Or.inr ⟨h, hR6⟩⟩
  · have hR4 : (degreeThree G R).card = 4 := by omega
    exact ⟨true, Or.inr ⟨hR4, h⟩⟩
  · have hR2 : (degreeThree G R).card = 2 := by omega
    exact ⟨true, Or.inl ⟨hR2, h⟩⟩

#print axioms twenty_one_high_parity_split

-- A half of size twenty-one inherits all the hypotheses of the signed slice obstruction.
private lemma twenty_one_half_slice {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (i : Fin 9) (b : Bool) (hsmall : (C.filter (fun x => x i = b)).card = 21) :
    ∃ S : Finset (Q 9), S.card = 21 ∧ IsBalanced S ∧
      let G := (hypercube 9).induce (S : Set (Q 9))
      (∀ v, G.degree v = 2 ∨ G.degree v = 3) ∧
        (degreeTwo G univ).card = 11 ∧
        (∀ ⦃v w⦄, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False) := by
  let p := Equiv.swap i (0 : Fin 9)
  let T := C.image (reindex p)
  let S := coordinateSlice T b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hreg' := reindex_regular hreg p
  have hb' := reindex_balanced hb p
  have ht : T.card = 66 := by
    simpa [T, card_image_of_injective _ (reindex p).injective] using hc
  have hsize : S.card = (C.filter (fun x => x i = b)).card := by
    dsimp [S, T, p]
    rw [reindex_slice, card_image_of_injective _ (reindex _).injective]
  have hdir : 6 * directionEdges T 0 = 66 := by
    simpa [ht] using direction_edge_count (d := 3) T hreg' hb' 0
  have htwo := low_slice_card_eq_q (b := b) hreg'
  change (degreeTwo G univ).card = directionEdges T 0 at htwo
  refine ⟨S, hsize.trans hsmall, balanced_subset hb' (filter_subset _ _),
    fun v => coordinate_slice_degree_cases v.property hreg', ?_, ?_⟩
  · change (degreeTwo G univ).card = 11
    rw [htwo]
    omega
  · intro v w hadj hv hw
    exact coordinate_slice_low_independent hreg' hb' hadj hv hw

#print axioms twenty_one_half_slice

private lemma smaller_half_deficits {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ (b : Fin 9 → Bool) (r : Fin 9 → ℤ),
      (∀ i, 0 ≤ r i ∧ r i ≤ 6) ∧
        ∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33 := by
  let b (i : Fin 9) : Bool := if (C.filter (fun x => x i = false)).card ≤ 33 then false else true
  let r (i : Fin 9) : ℤ := (33 - ((C.filter (fun x => x i = b i)).card : ℤ)) / 2
  have hsmall (i : Fin 9) : (C.filter (fun x => x i = b i)).card ≤ 33 := by
    have hs := card_filter_add_card_filter_not (s := C) (fun x => x i = false)
    have hn : (C.filter (fun x => ¬ x i = false)) = C.filter (fun x => x i = true) := by
      ext x
      cases x i <;> simp
    rw [hn,hc] at hs
    dsimp only [b]
    split_ifs <;> omega
  have hexact (i : Fin 9) : ((C.filter (fun x => x i = b i)).card : ℤ) + 2 * r i = 33 := by
    have ho := sixty_six_odd_coordinate_half hc hreg hb i (b i)
    have hs := hsmall i
    dsimp only [r]
    omega
  refine ⟨b,r,?_,hexact⟩
  intro i
  have hlo := sixty_six_half_card_ge_twenty_one hc hreg hb i (b i)
  have hhi := hsmall i
  have he := hexact i
  omega

private lemma coordinate_profile_for_partner_cap {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (cap : ℕ) (hcap : ∀ x ∈ C, (shell C x 7).card ≤ cap) :
    ∃ (b : Fin 9 → Bool) (r : Fin 9 → ℤ),
      (∀ i, 0 ≤ r i ∧ r i ≤ 6) ∧
      (∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33) ∧
      (∀ x ∈ C, (∑ i : Fin 9, if x i = b i then r i else 0) ≤ ((∑ i, r i) - 12 + cap) / 2) ∧
      110 * (∑ i, r i) ≤ 198 * (((∑ i, r i) - 12 + cap) / 2) + 6 * (∑ i, (r i)^2) := by
  obtain ⟨b,r,hrange,hr⟩ := smaller_half_deficits hc hreg hb
  let K : ℤ := ((∑ i, r i) - 12 + cap) / 2
  have hK (x : Q 9) (hx : x ∈ C) :
      (∑ i : Fin 9, if x i = b i then r i else 0) ≤ K := by
    have hp := coordinate_profile_weight_bound hc hreg hb b r hr hx
    have hcap' := hcap x hx
    dsimp only [K]
    omega
  exact ⟨b,r,hrange,hr,hK,coordinate_profile_moment_bound hc hreg hb b r K hr hK⟩

#print axioms coordinate_profile_for_partner_cap


/-- Enumerate nondecreasing coordinate deficits between `lower` and five. -/
private def orderedDeficits : ℕ → ℤ → List (List ℤ)
  | 0, _ => [[]]
  | n + 1, lower => (List.range 6).flatMap fun (i : ℕ) =>
      if lower ≤ (i : ℤ) then (orderedDeficits n i).map ((i : ℤ) :: ·) else []

private lemma orderedDeficits_complete {xs : List ℤ} {lower : ℤ}
    (hn : 0 ≤ lower) (hs : xs.Pairwise (· ≤ ·))
    (hb : ∀ x ∈ xs, lower ≤ x ∧ x ≤ 5) : xs ∈ orderedDeficits xs.length lower := by
  induction xs generalizing lower with
  | nil => simp [orderedDeficits]
  | cons x xs ih =>
    obtain ⟨hl, hu⟩ := hb x (by simp)
    have hx : 0 ≤ x := hn.trans hl
    have hc : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx
    have hr : x.toNat ∈ List.range 6 := List.mem_range.mpr (by omega)
    have hp := List.pairwise_cons.mp hs
    have ht := ih hx hp.2 (fun y hy => ⟨hp.1 y hy, (hb y (by simp [hy])).2⟩)
    simp only [List.length_cons, orderedDeficits, List.mem_flatMap]
    exact ⟨x.toNat, hr, by simpa [hc, hl] using ht⟩

private def capSixMoment (rs : List ℤ) : Prop :=
  110 * rs.sum ≤ 198 * ((rs.sum - 6) / 2) + 6 * (rs.map (fun r => r ^ 2)).sum

private instance (rs : List ℤ) : Decidable (capSixMoment rs) := by
  unfold capSixMoment
  infer_instance

-- These are the coordinate profiles covered by the proposed integer certificates.
private def capSixProfiles : List (List ℤ) := [
  [0, 0, 4, 5, 5, 5, 5, 5, 5],
  [0, 1, 5, 5, 5, 5, 5, 5, 5],
  [0, 2, 4, 5, 5, 5, 5, 5, 5],
  [0, 3, 3, 5, 5, 5, 5, 5, 5],
  [0, 3, 4, 4, 5, 5, 5, 5, 5],
  [0, 3, 5, 5, 5, 5, 5, 5, 5],
  [0, 4, 4, 5, 5, 5, 5, 5, 5],
  [0, 4, 5, 5, 5, 5, 5, 5, 5],
  [0, 5, 5, 5, 5, 5, 5, 5, 5],
  [1, 1, 4, 5, 5, 5, 5, 5, 5],
  [1, 2, 5, 5, 5, 5, 5, 5, 5],
  [1, 3, 4, 5, 5, 5, 5, 5, 5],
  [1, 4, 4, 4, 5, 5, 5, 5, 5],
  [1, 4, 5, 5, 5, 5, 5, 5, 5],
  [1, 5, 5, 5, 5, 5, 5, 5, 5],
  [2, 2, 4, 5, 5, 5, 5, 5, 5],
  [2, 3, 3, 5, 5, 5, 5, 5, 5],
  [2, 3, 4, 4, 5, 5, 5, 5, 5],
  [2, 3, 5, 5, 5, 5, 5, 5, 5],
  [2, 4, 4, 5, 5, 5, 5, 5, 5],
  [2, 4, 5, 5, 5, 5, 5, 5, 5],
  [2, 5, 5, 5, 5, 5, 5, 5, 5],
  [3, 3, 4, 5, 5, 5, 5, 5, 5],
  [3, 3, 5, 5, 5, 5, 5, 5, 5],
  [3, 4, 4, 4, 5, 5, 5, 5, 5],
  [3, 4, 4, 5, 5, 5, 5, 5, 5],
  [3, 4, 5, 5, 5, 5, 5, 5, 5],
  [3, 5, 5, 5, 5, 5, 5, 5, 5],
  [4, 4, 4, 4, 4, 5, 5, 5, 5],
  [4, 4, 4, 5, 5, 5, 5, 5, 5],
  [4, 4, 5, 5, 5, 5, 5, 5, 5],
  [4, 5, 5, 5, 5, 5, 5, 5, 5],
  [5, 5, 5, 5, 5, 5, 5, 5, 5]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
-- Kernel reduction checks every sorted tuple before taking the filter.
private lemma capSixProfiles_eq :
    (orderedDeficits 9 0).filter (fun rs => decide (capSixMoment rs)) = capSixProfiles := by
  decide +kernel

private lemma sum_ofFn_int {n : ℕ} (f : Fin n → ℤ) : (List.ofFn f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ, ih]

private lemma sorted_deficits_mem_capSixProfiles (r : Fin 9 → ℤ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 5)
    (hm : 110 * (∑ i, r i) ≤ 198 * (((∑ i, r i) - 6) / 2) + 6 * (∑ i, (r i) ^ 2)) :
    List.ofFn (r ∘ Tuple.sort r) ∈ capSixProfiles := by
  let rs := List.ofFn (r ∘ Tuple.sort r)
  have hb : ∀ x ∈ rs, 0 ≤ x ∧ x ≤ 5 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hr (Tuple.sort r i)
  have hsort : rs.Pairwise (· ≤ ·) := (Tuple.monotone_sort r).sortedLE_ofFn.pairwise
  have hsum : rs.sum = ∑ i, r i := by
    rw [sum_ofFn_int]
    exact Equiv.sum_comp (Tuple.sort r) r
  have hsumSq : (rs.map (fun x => x ^ 2)).sum = ∑ i, (r i)^2 := by
    rw [List.map_ofFn, sum_ofFn_int]
    exact Equiv.sum_comp (Tuple.sort r) (fun i => (r i)^2)
  rw [← capSixProfiles_eq, List.mem_filter, decide_eq_true_eq]
  refine ⟨by simpa [rs] using orderedDeficits_complete (le_refl 0) hsort hb, ?_⟩
  change capSixMoment rs
  simpa only [capSixMoment, hsum, hsumSq] using hm

private lemma coordinate_profile_in_capSixProfiles {C : Finset (Q 9)} (hc : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ (i : Fin 9) (v : Bool), 23 ≤ (C.filter (fun x => x i = v)).card)
    (hcap : ∀ x ∈ C, (shell C x 7).card ≤ 6) :
    ∃ (b : Fin 9 → Bool) (r : Fin 9 → ℤ),
      (∀ i, ((C.filter (fun y => y i = b i)).card : ℤ) + 2 * r i = 33) ∧
      (∀ x ∈ C, (∑ i : Fin 9, if x i = b i then r i else 0) ≤ ((∑ i, r i) - 6) / 2) ∧
      List.ofFn (r ∘ Tuple.sort r) ∈ capSixProfiles := by
  obtain ⟨b, r, hrange, hr, hw, hm⟩ := coordinate_profile_for_partner_cap hc hreg hb 6 hcap
  have hrange' (i : Fin 9) : 0 ≤ r i ∧ r i ≤ 5 := by
    have hlo : (23 : ℤ) ≤ (C.filter (fun x => x i = b i)).card := by exact_mod_cast hhalf i (b i)
    have hcard := hr i
    exact ⟨(hrange i).1, by omega⟩
  have ht : (∑ i, r i) - 12 + (6 : ℤ) = (∑ i, r i) - 6 := by omega
  simp only [Nat.cast_ofNat, ht] at hw hm
  exact ⟨b, r, hr, hw, sorted_deficits_mem_capSixProfiles r hrange' hm⟩

#print axioms coordinate_profile_in_capSixProfiles
