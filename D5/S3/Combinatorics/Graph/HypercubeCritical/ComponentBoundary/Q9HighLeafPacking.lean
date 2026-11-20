/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9HighLeafPacking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9HighLeafPacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed row packing bounds the number of high leaves at a common exterior mate. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal

/-! High leaves of a cubic balanced Q9 support have a unique exterior neighbor. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9HighLeafPacking

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj gamma_apply IsSwitching)
open BalancedCubeGirth (gamma_anticommute)
open BalancedCubeComponentBoundary (directions exterior_even regular_directions)
open SupportedEigenSaturation (matrix_sq_of_adj)
open Q9EightfoldCoverLocal (transverseSign card_transverse_signs)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flip_comm from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private transverseSign_unit sign_neg_of_corner sign_transport from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal

local notation "flip" => BalancedCriticalSpectrum.flip

open Classical in
/-- Directions from a mate to exterior vertices whose eight transverse neighbors are selected. -/
def highLeafDirections (C : Finset (Q 9)) (x : Q 9) : Finset (Fin 9) :=
  Finset.univ.filter fun i => flip x i ∉ C ∧ ∀ j ≠ i, flip (flip x i) j ∈ C

private theorem mem_highLeafDirections {C : Finset (Q 9)} {x : Q 9} {i : Fin 9} :
    i ∈ highLeafDirections C x ↔
      flip x i ∉ C ∧ ∀ j ≠ i, flip (flip x i) j ∈ C := by
  simp [highLeafDirections]

private def rowSign (sigma : Q 9 → ℝ) (x : Q 9) (i j : Fin 9) : ℝ :=
  huangMatrix 9 x (flip x i) * transverseSign sigma (flip x i) j

open Classical in
private def positiveAxes (sigma : Q 9 → ℝ) (x : Q 9) (i : Fin 9) : Finset (Fin 9) :=
  (Finset.univ.erase i).filter fun j => rowSign sigma x i j = 1

private theorem mem_positiveAxes {sigma : Q 9 → ℝ} {x : Q 9} {i j : Fin 9} :
    j ∈ positiveAxes sigma x i ↔ j ≠ i ∧ rowSign sigma x i j = 1 := by
  simp [positiveAxes]

variable {C : Finset (Q 9)} {sigma : Q 9 → ℝ} {x : Q 9} {i j : Fin 9}

open Classical in
private theorem card_positiveAxes
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : x ∉ C) (hi : i ∈ highLeafDirections C x) :
    (positiveAxes sigma x i).card = 4 := by
  obtain ⟨hout, hcover⟩ := mem_highLeafDirections.mp hi
  have hcounts := card_transverse_signs hr hs hout
    (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx) hcover
  have hfactor := sq_eq_one_iff.mp (matrix_sq_of_adj (flip_adj x i))
  rcases hfactor with h | h
  · simpa only [positiveAxes, rowSign, h, one_mul] using hcounts.1
  · simpa only [positiveAxes, rowSign, h, neg_mul, one_mul, neg_eq_iff_eq_neg]
      using hcounts.2

private theorem rowSign_unit (hs : IsSwitching C sigma)
    (hi : i ∈ highLeafDirections C x) (hji : j ≠ i) :
    rowSign sigma x i j = 1 ∨ rowSign sigma x i j = -1 := by
  have hfactor := sq_eq_one_iff.mp (matrix_sq_of_adj (flip_adj x i))
  have hsign := transverseSign_unit hs ((mem_highLeafDirections.mp hi).2 j hji)
  rcases hfactor with h | h <;> rcases hsign with h' | h' <;> norm_num [rowSign, h, h']

private theorem rowSign_antisymm (hij : i ≠ j) :
    rowSign sigma x i j = -rowSign sigma x j i := by
  simpa only [Pi.neg_apply, gamma_apply, rowSign, transverseSign] using
    congrFun (gamma_anticommute hij sigma) x

private theorem mem_positiveAxes_of_selected_axis (hs : IsSwitching C sigma)
    (hi : i ∈ highLeafDirections C x) (hj : flip x j ∈ C) :
    j ∈ positiveAxes sigma x i ↔ -transverseSign sigma x j = 1 := by
  obtain ⟨hout, hcover⟩ := mem_highLeafDirections.mp hi
  have hji : j ≠ i := fun e => hout (e ▸ hj)
  rw [mem_positiveAxes, and_iff_right hji]
  change (huangMatrix 9 x (flip x i) * transverseSign sigma (flip x i) j = 1) ↔ _
  rw [sign_transport hs hji hj (hcover j hji), neg_neg]

open Classical in
private theorem three_axes_in_positive_difference
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hi : i ∈ highLeafDirections C x)
    (hj : j ∈ highLeafDirections C x) (hij : i ≠ j) (hpos : rowSign sigma x i j = 1) :
    3 ≤ (positiveAxes sigma x j \ positiveAxes sigma x i).card := by
  obtain ⟨hiOut, hiCover⟩ := mem_highLeafDirections.mp hi
  obtain ⟨hjOut, hjCover⟩ := mem_highLeafDirections.mp hj
  let p := flip (flip x i) j
  have hp : p ∈ C := hiCover j hij.symm
  have hneg : rowSign sigma x j i = -1 := by
    rw [rowSign_antisymm hij.symm, hpos]
  rw [← regular_directions C hr hp]
  apply Finset.card_le_card
  intro k hk
  have htriple := (mem_directions C p k).mp hk
  have hki : k ≠ i := by
    intro h
    subst k
    apply hjOut
    simpa only [p, flip_comm x i j, BalancedCriticalSpectrum.flip_flip] using htriple
  have hkj : k ≠ j := by
    intro h
    subst k
    exact hiOut (by simpa only [p, BalancedCriticalSpectrum.flip_flip] using htriple)
  have hiSign : rowSign sigma x i j = -rowSign sigma x i k := by
    unfold rowSign
    rw [sign_neg_of_corner hs hkj.symm hp (hiCover k hki) htriple, mul_neg]
  have hp' : flip (flip x j) i ∈ C := by simpa only [flip_comm x j i] using hp
  have htriple' : flip (flip (flip x j) i) k ∈ C := by
    simpa only [flip_comm x j i] using htriple
  have hjSign : rowSign sigma x j i = -rowSign sigma x j k := by
    unfold rowSign
    rw [sign_neg_of_corner hs hki.symm hp' (hjCover k hkj) htriple', mul_neg]
  rw [hpos] at hiSign
  rw [hneg] at hjSign
  exact Finset.mem_sdiff.mpr
    ⟨mem_positiveAxes.mpr ⟨hkj, by linarith only [hjSign]⟩,
      fun hm => by linarith only [hiSign, (mem_positiveAxes.mp hm).2]⟩

open Classical in
private theorem card_positiveAxes_inter_le_one
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : x ∉ C)
    (hi : i ∈ highLeafDirections C x) (hj : j ∈ highLeafDirections C x) (hij : i ≠ j) :
    (positiveAxes sigma x i ∩ positiveAxes sigma x j).card ≤ 1 := by
  rcases rowSign_unit hs hi hij.symm with h | h
  · have hdiff := three_axes_in_positive_difference hr hs hi hj hij h
    have hcount := Finset.card_sdiff_add_card_inter
      (positiveAxes sigma x j) (positiveAxes sigma x i)
    rw [Finset.inter_comm, card_positiveAxes hr hs hx hj] at hcount
    omega
  · have h' : rowSign sigma x j i = 1 := by rw [rowSign_antisymm hij.symm, h, neg_neg]
    have hdiff := three_axes_in_positive_difference hr hs hj hi hij.symm h'
    have hcount := Finset.card_sdiff_add_card_inter
      (positiveAxes sigma x i) (positiveAxes sigma x j)
    rw [card_positiveAxes hr hs hx hi] at hcount
    omega

private theorem three_rows_fill {A B E : Finset (Fin 9)}
    (hA : A.card = 4) (hB : B.card = 4) (hE : E.card = 4)
    (hAB : (A ∩ B).card ≤ 1) (hEA : (E ∩ A).card ≤ 1) (hEB : (E ∩ B).card ≤ 1) :
    (A ∪ B) ∪ E = Finset.univ ∧ (E ∩ A) ∩ (E ∩ B) = ∅ := by
  have hABCount := Finset.card_union_add_card_inter A B
  have hUnion := Finset.card_union_add_card_inter (A ∪ B) E
  rw [Finset.inter_comm (A ∪ B) E, Finset.inter_union_distrib_left] at hUnion
  have hInter := Finset.card_union_add_card_inter (E ∩ A) (E ∩ B)
  have hle := Finset.card_le_card (Finset.subset_univ ((A ∪ B) ∪ E))
  rw [Finset.card_univ, Fintype.card_fin] at hle
  refine ⟨Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_,
    Finset.card_eq_zero.mp (by omega)⟩
  rw [Finset.card_univ, Fintype.card_fin]
  omega

open Classical in
/-- An exterior mate has at most three high leaves. -/
theorem card_highLeafDirections_le_three
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : x ∉ C) :
    (highLeafDirections C x).card ≤ 3 := by
  by_contra! h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    Finset.three_lt_card.mp h
  let O := positiveAxes sigma x
  have hcard {k : Fin 9} (hk : k ∈ highLeafDirections C x) : (O k).card = 4 :=
    card_positiveAxes hr hs hx hk
  have hinter {k l : Fin 9} (hk : k ∈ highLeafDirections C x)
      (hl : l ∈ highLeafDirections C x) (hkl : k ≠ l) : (O k ∩ O l).card ≤ 1 :=
    card_positiveAxes_inter_le_one hr hs hx hk hl hkl
  have hfill := (three_rows_fill (hcard ha) (hcard hb) (hcard hc)
    (hinter ha hb hab) (hinter hc ha hac.symm) (hinter hc hb hbc.symm)).1
  have hdecomp : O d = ((O d ∩ O a) ∪ (O d ∩ O b)) ∪ (O d ∩ O c) := by
    rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left, hfill,
      Finset.inter_univ]
  have htwo := Finset.card_union_le (O d ∩ O a) (O d ∩ O b)
  have hthree := Finset.card_union_le ((O d ∩ O a) ∪ (O d ∩ O b)) (O d ∩ O c)
  rw [← hdecomp, hcard hd] at hthree
  have hda := hinter hd ha had.symm
  have hdb := hinter hd hb hbd.symm
  have hdc := hinter hd hc hcd.symm
  omega

open Classical in
private theorem directions_eq_empty_of_three_le
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : x ∉ C)
    (h : 3 ≤ (highLeafDirections C x).card) : directions C x = ∅ := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h
  let O := positiveAxes sigma x
  obtain ⟨hfill, hEmpty⟩ := three_rows_fill
    (card_positiveAxes hr hs hx ha) (card_positiveAxes hr hs hx hb)
    (card_positiveAxes hr hs hx hc)
    (card_positiveAxes_inter_le_one hr hs hx ha hb hab)
    (card_positiveAxes_inter_le_one hr hs hx hc ha hac.symm)
    (card_positiveAxes_inter_le_one hr hs hx hc hb hbc.symm)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hkC := (mem_directions C x k).mp hk
  have hmem {l : Fin 9} (hl : l ∈ highLeafDirections C x) :
      k ∈ O l ↔ -transverseSign sigma x k = 1 :=
    mem_positiveAxes_of_selected_axis hs hl hkC
  have hkUnion : k ∈ (O a ∪ O b) ∪ O c := hfill ▸ Finset.mem_univ k
  simp only [Finset.mem_union, hmem ha, hmem hb, hmem hc, or_self] at hkUnion
  have hcommon : k ∈ (O c ∩ O a) ∩ (O c ∩ O b) :=
    Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(hmem hc).mpr hkUnion, (hmem ha).mpr hkUnion⟩,
      Finset.mem_inter.mpr ⟨(hmem hc).mpr hkUnion, (hmem hb).mpr hkUnion⟩⟩
  exact Finset.notMem_empty k (hEmpty ▸ hcommon)

open Classical in
private theorem card_directions_le_two_of_positive_pair
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : x ∉ C)
    (hi : i ∈ highLeafDirections C x) (hj : j ∈ highLeafDirections C x)
    (hij : i ≠ j) (hpos : rowSign sigma x i j = 1) : (directions C x).card ≤ 2 := by
  let A := positiveAxes sigma x i
  let B := positiveAxes sigma x j
  let agree := (A ∩ B) ∪ (Finset.univ \ (A ∪ B))
  have hcount := Finset.card_union_add_card_inter A B
  have hA : A.card = 4 := card_positiveAxes hr hs hx hi
  have hB : B.card = 4 := card_positiveAxes hr hs hx hj
  have hInter : (A ∩ B).card ≤ 1 := card_positiveAxes_inter_le_one hr hs hx hi hj hij
  have hCompl := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A ∪ B))
  rw [Finset.card_univ, Fintype.card_fin] at hCompl
  have hAgree : agree.card ≤ 3 := by
    have hle := Finset.card_union_le (A ∩ B) (Finset.univ \ (A ∪ B))
    change agree.card ≤ _ at hle
    omega
  have hiA : i ∉ A := fun h => (mem_positiveAxes.mp h).1 rfl
  have hiB : i ∉ B := by
    intro h
    have hsign := (mem_positiveAxes.mp h).2
    rw [rowSign_antisymm hij.symm, hpos] at hsign
    norm_num at hsign
  have hiAgree : i ∈ agree :=
    Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hiA hiB⟩)
  have hiOut : i ∉ directions C x := fun h =>
    (mem_highLeafDirections.mp hi).1 ((mem_directions C x i).mp h)
  have hsub : insert i (directions C x) ⊆ agree := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hiAgree
    have hkC := (mem_directions C x k).mp hk
    have hmem {l : Fin 9} (hl : l ∈ highLeafDirections C x) :
        k ∈ positiveAxes sigma x l ↔ -transverseSign sigma x k = 1 :=
      mem_positiveAxes_of_selected_axis hs hl hkC
    by_cases hsign : -transverseSign sigma x k = 1
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨(hmem hi).mpr hsign, (hmem hj).mpr hsign⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
          (fun hA => hsign ((hmem hi).mp hA)) (fun hB => hsign ((hmem hj).mp hB))⟩)
  have hle := (Finset.card_le_card hsub).trans hAgree
  rw [Finset.card_insert_of_notMem hiOut] at hle
  omega

open Classical in
private theorem card_directions_le_two_of_two_le
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : x ∉ C) (h : 2 ≤ (highLeafDirections C x).card) :
    (directions C x).card ≤ 2 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h
  rcases rowSign_unit hs hi hij.symm with hpos | hneg
  · exact card_directions_le_two_of_positive_pair hr hs hx hi hj hij hpos
  · apply card_directions_le_two_of_positive_pair hr hs hx hj hi hij.symm
    rw [rowSign_antisymm hij.symm, hneg, neg_neg]

open Classical in
/-- The high-leaf cap is three, two, or one at an exterior mate with respectively
zero, two, or at least four selected neighbors. -/
theorem card_highLeafDirections_le_by_degree
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : x ∉ C) :
    (highLeafDirections C x).card ≤
      if (directions C x).card = 0 then 3 else if (directions C x).card = 2 then 2 else 1 := by
  split_ifs with hzero htwo
  · exact card_highLeafDirections_le_three hr hs hx
  · by_contra! h
    have hEmpty := directions_eq_empty_of_three_le hr hs hx h
    exact hzero (by simp [hEmpty])
  · by_contra! h
    have hsmall := card_directions_le_two_of_two_le hr hs hx h
    obtain ⟨n, hn⟩ := exterior_even C hr ⟨sigma, hs⟩ x hx
    omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9HighLeafPacking
