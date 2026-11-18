/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/EightUniformHeightSpan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/EightUniformHeightSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Eight actual uniform directions force centered signed-height span at most one. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiftyFourLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCounting
import Batteries.Tactic.OpenPrivate

/-! Private signed-height geometry consumed by actual Gray reconstruction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false
noncomputable section
namespace D5.S3.Combinatorics.Graph.HypercubeCritical.EightUniformHeightSpan

open scoped BigOperators
attribute [local instance] Classical.propDecidable
open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced directionEdges direction_edge_count)
open BalancedCriticalSpectrum (flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private balanced_subset paritySide parity_bipartite parity_union from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private side_spectrum from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCounting
open private degreeSlice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCounting
open GirthSliceCounting
local notation "flip" => BalancedCriticalSpectrum.flip

private abbrev Q9 := Q 9
private abbrev Coord := Fin 9

private def kappa (j : Coord) (x : Q9) : Q9 :=
  if x j = false then x else flip x j

private theorem kappa_eq_or {j : Coord} {x y : Q9}
    (h : kappa j x = kappa j y) : y = x ∨ y = flip x j := by
  by_cases hx : x j = false <;> by_cases hy : y j = false
  · left
    simpa [kappa, hx, hy] using h.symm
  · right
    have hh : x = flip y j := by simpa [kappa, hx, hy] using h
    have := congrArg (fun z => flip z j) hh
    simpa only [BalancedCriticalSpectrum.flip_flip] using this.symm
  · right
    have hh : flip x j = y := by simpa [kappa, hx, hy] using h
    exact hh.symm
  · left
    have h' : flip x j = flip y j := by simpa [kappa, hx, hy] using h
    have hh : flip (flip x j) j = flip (flip y j) j :=
      congrArg (fun z => flip z j) h'
    apply Eq.symm
    simpa only [BalancedCriticalSpectrum.flip_flip] using hh

private def mismatchSet (j : Coord) (a : Coord → Bool) (x : Q9) : Finset Coord :=
  (Finset.univ.erase j).filter (fun i => x i ≠ a i)

private def weight (j : Coord) (a : Coord → Bool) (x : Q9) : Nat :=
  (mismatchSet j a x).card

private def centeredHeight (j : Coord) (a : Coord → Bool) (x : Q9) : Int :=
  (weight j a x : Int) - if cubeParity x then 1 else 0

private theorem mismatch_step_non_j {C : Finset Q9} {j : Coord} {a : Coord → Bool}
    (ha : ∀ i, i ≠ j → ∀ x ∈ C, cubeParity x = false → flip x i ∈ C → x i = a i)
    {x : Q9} (hx : x ∈ C) (i : Coord) (hiC : flip x i ∈ C)
    (hi : i ≠ j) (hp : cubeParity x = false) :
    weight j a (flip x i) = weight j a x + 1 := by
  have hu := ha i hi x hx hp hiC
  have hnot : i ∉ mismatchSet j a x := by
    simp [mismatchSet, hi, hu]
  have heq : mismatchSet j a (flip x i) = insert i (mismatchSet j a x) := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [mismatchSet, hi, hu]
    · simp [mismatchSet, hk, BalancedCriticalSpectrum.flip]
  change (mismatchSet j a (flip x i)).card = (mismatchSet j a x).card + 1
  rw [heq, Finset.card_insert_of_notMem hnot]

private theorem height_flip_non_j {C : Finset Q9} {j : Coord} {a : Coord → Bool}
    (ha : ∀ i, i ≠ j → ∀ x ∈ C, cubeParity x = false → flip x i ∈ C → x i = a i)
    {x : Q9} (hx : x ∈ C) (i : Coord) (hi : i ≠ j) (hiC : flip x i ∈ C) :
    centeredHeight j a (flip x i) = centeredHeight j a x := by
  by_cases hp : cubeParity x = false
  · have hw := mismatch_step_non_j ha hx i hiC hi hp
    unfold centeredHeight
    have hpar := cubeParity_ne_of_adj (flip_adj x i)
    have htrue : cubeParity (flip x i) = true := by
      cases hq : cubeParity (flip x i) <;> simp_all
    simp [hp, htrue]
    omega
  · have hp' : cubeParity (flip x i) = false := by
      have hpar := cubeParity_ne_of_adj (flip_adj (flip x i) i)
      cases hq : cubeParity (flip x i) <;> cases hr : cubeParity x <;> simp_all
    have hw := mismatch_step_non_j ha hiC i (by simpa using hx) hi hp'
    have hback : weight j a x = weight j a (flip x i) + 1 := by
      have hw' : weight j a x = weight j a (flip x i) + 1 := by
        simpa only [BalancedCriticalSpectrum.flip_flip] using hw
      exact hw'
    unfold centeredHeight
    have htrue : cubeParity x = true := by cases hxpar : cubeParity x <;> simp_all
    simp [hp', htrue]
    omega

private theorem height_step {C : Finset Q9} {j : Coord} {a : Coord → Bool}
    (ha : ∀ i, i ≠ j → ∀ x ∈ C, cubeParity x = false → flip x i ∈ C → x i = a i)
    {x : Q9} (hx : x ∈ C) (i : Coord) (hiC : flip x i ∈ C) :
    (i = j ∧ cubeParity x = false ∧
        centeredHeight j a (flip x i) = centeredHeight j a x - 1) ∨
      (i = j ∧ cubeParity x = true ∧
        centeredHeight j a (flip x i) = centeredHeight j a x + 1) ∨
      (i ≠ j ∧ centeredHeight j a (flip x i) = centeredHeight j a x) := by
  by_cases hij : i = j
  · subst j
    by_cases hp : cubeParity x = false
    · have hne : weight i a (flip x i) = weight i a x := by
        have heq : mismatchSet i a (flip x i) = mismatchSet i a x := by
          apply Finset.filter_congr
          intro k hk
          by_cases hki : k = i
          · subst k; exact ((Finset.mem_erase.mp hk).1 rfl).elim
          · simp [mismatchSet, hki, BalancedCriticalSpectrum.flip]
        simp [weight, heq]
      unfold centeredHeight
      have htrue : cubeParity (flip x i) = true := by
        have hn := cubeParity_ne_of_adj (flip_adj x i)
        cases hq : cubeParity (flip x i) <;> simp_all
      simp [hp, htrue, hne]
    · have hp' : cubeParity (flip x i) = false := by
        have hn := cubeParity_ne_of_adj (flip_adj x i)
        cases hq : cubeParity (flip x i) <;> cases hr : cubeParity x <;> simp_all
      have hne : weight i a (flip x i) = weight i a x := by
        have heq : mismatchSet i a (flip x i) = mismatchSet i a x := by
          apply Finset.filter_congr
          intro k hk
          by_cases hki : k = i
          · subst k; exact ((Finset.mem_erase.mp hk).1 rfl).elim
          · simp [mismatchSet, hki, BalancedCriticalSpectrum.flip]
        simp [weight, heq]
      unfold centeredHeight
      have htrue : cubeParity x = true := by cases hxpar : cubeParity x <;> simp_all
      simp [hp', htrue, hne]
  · exact Or.inr (Or.inr ⟨hij, height_flip_non_j ha hx i hij hiC⟩)

private theorem induced_degree_eq_neighbor_card (S : Finset Q9)
    (x : (S : Set Q9)) :
    ((hypercube 9).induce (S : Set Q9)).degree x =
      ((hypercube 9).neighborFinset x.1 ∩ S).card := by
  have himage : ((((hypercube 9).induce (S : Set Q9)).neighborFinset x).image
      (fun y => y.1)) = (hypercube 9).neighborFinset x.1 ∩ S := by
    ext y
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_inter]
    change (∃ a : (S : Set Q9), (hypercube 9).Adj x.1 a.1 ∧ a.1 = y) ↔ _
    constructor
    · rintro ⟨a, hxy, rfl⟩
      exact ⟨hxy, a.property⟩
    · rintro ⟨hxy, hy⟩
      exact ⟨⟨y, hy⟩, hxy, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

private theorem lower_bound_neighbor_closed {C A : Finset Q9}
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hA : A.Nonempty) (hsub : A ⊆ C)
    (hclosed : ∀ x ∈ A, ∀ y ∈ C, (hypercube 9).Adj x y → y ∈ A) :
    54 ≤ A.card := by
  have hrA : ((hypercube 9).induce (A : Set Q9)).IsRegularOfDegree 3 := by
    intro x
    have hxC : x.1 ∈ C := hsub x.2
    have heq : (hypercube 9).neighborFinset x.1 ∩ A =
        (hypercube 9).neighborFinset x.1 ∩ C := by
      ext y
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hxy, hy⟩
        exact ⟨hxy, hsub hy⟩
      · rintro ⟨hxy, hy⟩
        exact ⟨hxy, hclosed x.1 x.2 y hy hxy⟩
    rw [induced_degree_eq_neighbor_card, heq]
    have hrd := hr.degree_eq ⟨x.1, hxC⟩
    rw [induced_degree_eq_neighbor_card] at hrd
    exact hrd
  have hbA : IsBalanced A := balanced_subset hb hsub
  by_contra hlt
  exact BalancedCubeFiftyFourLowerBound.result ⟨A, hA, hrA, hbA, by omega⟩

set_option maxHeartbeats 1000000 in
private theorem height_span {C : Finset Q9}
    (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcard : C.card = 54) (j : Coord) (a : Coord → Bool)
    (ha : ∀ i, i ≠ j → ∀ x ∈ C, cubeParity x = false →
      flip x i ∈ C → x i = a i) :
    ∀ x ∈ C, ∀ y ∈ C, centeredHeight j a x ≤ centeredHeight j a y + 1 := by
  classical
  let h : Q9 → Int := centeredHeight j a
  let H : Finset Int := C.image h
  have hH : H.Nonempty := by
    obtain ⟨x, hx⟩ := hC
    exact ⟨h x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let m : Int := H.min' hH
  let M : Int := H.max' hH
  have hmin_mem : m ∈ H := by
    exact Finset.min'_mem H hH
  have hmax_mem : M ∈ H := by
    exact Finset.max'_mem H hH
  have hmin_le (x : Q9) (hx : x ∈ C) : m ≤ h x := by
    exact Finset.min'_le H (h x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hle_max (x : Q9) (hx : x ∈ C) : h x ≤ M := by
    exact Finset.le_max' H (h x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  let A := C.filter (fun x => h x = m)
  let B := C.filter (fun x => h x = M)
  have hA_nonempty : A.Nonempty := by
    obtain ⟨v, hv⟩ := Finset.mem_image.mp hmin_mem
    exact ⟨v, Finset.mem_filter.mpr ⟨hv.1, hv.2⟩⟩
  have hB_nonempty : B.Nonempty := by
    obtain ⟨v, hv⟩ := Finset.mem_image.mp hmax_mem
    exact ⟨v, Finset.mem_filter.mpr ⟨hv.1, hv.2⟩⟩
  have hstep' {x : Q9} (hx : x ∈ C) (i : Coord) (hiC : flip x i ∈ C) :
      (i = j ∧ cubeParity x = false ∧ h (flip x i) = h x - 1) ∨
        (i = j ∧ cubeParity x = true ∧ h (flip x i) = h x + 1) ∨
        (i ≠ j ∧ h (flip x i) = h x) := by
    exact height_step ha hx i hiC
  have hspan : ¬ M - m ≥ 2 := by
    intro hspan
    have hABdisj : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      have hxm := (Finset.mem_filter.mp hxA).2
      have hxM := (Finset.mem_filter.mp hxB).2
      omega
    have hAproper : A.card < C.card := by
      obtain ⟨x, hx⟩ := hB_nonempty
      have hnot : x ∉ A := by
        intro hxa
        exact (Finset.disjoint_left.mp hABdisj hxa hx).elim
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.filter_subset _ _, fun heq =>
          hnot (heq.symm ▸ (Finset.mem_filter.mp hx).1)⟩)
    have hBproper : B.card < C.card := by
      obtain ⟨x, hx⟩ := hA_nonempty
      have hnot : x ∉ B := by
        intro hxb
        exact (Finset.disjoint_left.mp hABdisj hx hxb).elim
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.filter_subset _ _, fun heq =>
          hnot (heq.symm ▸ (Finset.mem_filter.mp hx).1)⟩)
    have hA_neighbor_cases (x : Q9) (hxA : x ∈ A) {y : Q9}
        (hyC : y ∈ C) (hxy : (hypercube 9).Adj x y) :
        y ∈ A ∨ (y = flip x j ∧ cubeParity x = true) := by
      obtain ⟨i, hi⟩ := adjacent_exists_flip hxy
      subst y
      rcases hstep' (Finset.mem_filter.mp hxA).1 i hyC with hi | hi | hi
      · have hlo := hmin_le (flip x i) hyC
        have hxm := (Finset.mem_filter.mp hxA).2
        omega
      · exact Or.inr ⟨by rw [hi.1], hi.2.1⟩
      · left
        apply Finset.mem_filter.mpr
        exact ⟨hyC, by rw [hi.2, (Finset.mem_filter.mp hxA).2]⟩
    have hB_neighbor_cases (x : Q9) (hxB : x ∈ B) {y : Q9}
        (hyC : y ∈ C) (hxy : (hypercube 9).Adj x y) :
        y ∈ B ∨ (y = flip x j ∧ cubeParity x = false) := by
      obtain ⟨i, hi⟩ := adjacent_exists_flip hxy
      subst y
      rcases hstep' (Finset.mem_filter.mp hxB).1 i hyC with hi | hi | hi
      · exact Or.inr ⟨by rw [hi.1], hi.2.1⟩
      · have hhi := hle_max (flip x i) hyC
        have hxm := (Finset.mem_filter.mp hxB).2
        omega
      · left
        apply Finset.mem_filter.mpr
        exact ⟨hyC, by rw [hi.2, (Finset.mem_filter.mp hxB).2]⟩
    have hAdeg (x : Q9) (hxA : x ∈ A) :
        ((hypercube 9).induce (A : Set Q9)).degree ⟨x, hxA⟩ = 2 ∨
          ((hypercube 9).induce (A : Set Q9)).degree ⟨x, hxA⟩ = 3 := by
      rw [induced_degree_eq_neighbor_card]
      let N : Finset Q9 := (hypercube 9).neighborFinset x ∩ C
      let I : Finset Q9 := (hypercube 9).neighborFinset x ∩ A
      have hN : N.card = 3 := by
        rw [← induced_degree_eq_neighbor_card C ⟨x, (Finset.mem_filter.mp hxA).1⟩]
        exact hr.degree_eq _
      have hsubI : I ⊆ N := by
        intro y hy
        simp only [I, N, Finset.mem_inter] at hy ⊢
        exact ⟨hy.1, (Finset.mem_filter.mp hy.2).1⟩
      let D : Finset Q9 := N.filter (fun y => y ∉ I)
      have hsubD : D ⊆ ({flip x j} : Finset Q9) := by
        intro y hy
        have hyD := Finset.mem_filter.mp hy
        have hyC := (Finset.mem_inter.mp hyD.1).2
        have hxy := (Finset.mem_inter.mp hyD.1).1
        have hxy' : (hypercube 9).Adj x y :=
          ((hypercube 9).mem_neighborFinset x y).mp hxy
        rcases hA_neighbor_cases x hxA hyC hxy' with hyA | hyj
        · exact (hyD.2 (Finset.mem_inter.mpr ⟨hxy, hyA⟩)).elim
        · exact Finset.mem_singleton.mpr hyj.1
      have hdiff : D.card ≤ 1 := by simpa using Finset.card_le_card hsubD
      have hcardI : I.card + D.card = N.card := by
        have hh := Finset.card_filter_add_card_filter_not (s := N)
          (p := fun y => y ∈ I)
        have hfilter : N.filter (fun y => y ∈ I) = I := by
          ext y
          simp [hsubI]
        simpa [D, hfilter, Nat.add_comm] using hh
      have hcardI' : I.card + D.card = 3 := hcardI.trans hN
      have hI : I.card ≥ 2 := by omega
      have hI3 : I.card ≤ 3 := by omega
      change I.card = 2 ∨ I.card = 3
      omega
    have hBdeg (x : Q9) (hxB : x ∈ B) :
        ((hypercube 9).induce (B : Set Q9)).degree ⟨x, hxB⟩ = 2 ∨
          ((hypercube 9).induce (B : Set Q9)).degree ⟨x, hxB⟩ = 3 := by
      rw [induced_degree_eq_neighbor_card]
      let N : Finset Q9 := (hypercube 9).neighborFinset x ∩ C
      let I : Finset Q9 := (hypercube 9).neighborFinset x ∩ B
      have hN : N.card = 3 := by
        rw [← induced_degree_eq_neighbor_card C ⟨x, (Finset.mem_filter.mp hxB).1⟩]
        exact hr.degree_eq _
      have hsubI : I ⊆ N := by
        intro y hy
        simp only [I, N, Finset.mem_inter] at hy ⊢
        exact ⟨hy.1, (Finset.mem_filter.mp hy.2).1⟩
      let D : Finset Q9 := N.filter (fun y => y ∉ I)
      have hsubD : D ⊆ ({flip x j} : Finset Q9) := by
        intro y hy
        have hyD := Finset.mem_filter.mp hy
        have hyC := (Finset.mem_inter.mp hyD.1).2
        have hxy := (Finset.mem_inter.mp hyD.1).1
        have hxy' : (hypercube 9).Adj x y :=
          ((hypercube 9).mem_neighborFinset x y).mp hxy
        rcases hB_neighbor_cases x hxB hyC hxy' with hyB | hyj
        · exact (hyD.2 (Finset.mem_inter.mpr ⟨hxy, hyB⟩)).elim
        · exact Finset.mem_singleton.mpr hyj.1
      have hdiff : D.card ≤ 1 := by simpa using Finset.card_le_card hsubD
      have hcardI : I.card + D.card = N.card := by
        have hh := Finset.card_filter_add_card_filter_not (s := N)
          (p := fun y => y ∈ I)
        have hfilter : N.filter (fun y => y ∈ I) = I := by
          ext y
          simp [hsubI]
        simpa [D, hfilter, Nat.add_comm] using hh
      have hcardI' : I.card + D.card = 3 := hcardI.trans hN
      have hI : I.card ≥ 2 := by omega
      have hI3 : I.card ≤ 3 := by omega
      change I.card = 2 ∨ I.card = 3
      omega
    have hAclosed_if (hzero : ∀ x ∈ A, ∀ y ∈ C,
        (hypercube 9).Adj x y → y ∈ A) : False := by
      have hlow := lower_bound_neighbor_closed hr hb hA_nonempty
        (Finset.filter_subset _ _) hzero
      omega
    have hAqpos : ∃ x ∈ A, flip x j ∈ C ∧ flip x j ∉ A := by
      by_contra hn
      exact hAclosed_if (by
        intro x hx y hy hxy
        rcases hA_neighbor_cases x hx hy hxy with hxa | hxb
        · exact hxa
        · have hnot : flip x j ∉ A := by
            intro hm
            have hm' := (Finset.mem_filter.mp hm).2
            have hx' := (Finset.mem_filter.mp hx).2
            have hjC : flip x j ∈ C := hxb.1 ▸ hy
            have hlow := hmin_le (flip x j) hjC
            have hrel := hstep' (Finset.mem_filter.mp hx).1 j hjC
            rcases hrel with ⟨_, _, hval⟩ | ⟨_, _, hval⟩ | hne
            · rw [hm', hx'] at hval
              omega
            · rw [hm', hx'] at hval
              omega
            · exact (hne.1 rfl).elim
          exact (hn ⟨x, hx, hxb.1 ▸ hy, hnot⟩).elim)
    have hBqpos : ∃ x ∈ B, flip x j ∈ C ∧ flip x j ∉ B := by
      by_contra hn
      have hBclosed_if : ∀ x ∈ B, ∀ y ∈ C,
          (hypercube 9).Adj x y → y ∈ B := by
        intro x hx y hy hxy
        rcases hB_neighbor_cases x hx hy hxy with hxb | hxc
        · exact hxb
        · have hnot : flip x j ∉ B := by
            intro hm
            have hm' := (Finset.mem_filter.mp hm).2
            have hx' := (Finset.mem_filter.mp hx).2
            have hjC : flip x j ∈ C := hxc.1 ▸ hy
            have hhigh := hle_max (flip x j) hjC
            have hrel := hstep' (Finset.mem_filter.mp hx).1 j hjC
            rcases hrel with ⟨_, _, hval⟩ | ⟨_, _, hval⟩ | hne
            · rw [hm', hx'] at hval
              omega
            · rw [hm', hx'] at hval
              omega
            · exact (hne.1 rfl).elim
          exact (hn ⟨x, hx, hxc.1 ▸ hy, hnot⟩).elim
      have hlow := lower_bound_neighbor_closed hr hb hB_nonempty
        (Finset.filter_subset _ _) hBclosed_if
      omega

    have hbA : IsBalanced A := balanced_subset hb (Finset.filter_subset _ _)
    have hbB : IsBalanced B := balanced_subset hb (Finset.filter_subset _ _)
    let GA := (hypercube 9).induce (A : Set Q9)
    let GB := (hypercube 9).induce (B : Set Q9)
    let LA := paritySide A false
    let RA := paritySide A true
    let LB := paritySide B true
    let RB := paritySide B false
    have hpartA : GA.IsBipartiteWith (LA : Set _) (RA : Set _) := by
      simpa [GA, LA, RA] using parity_bipartite A
    have hcoverA : LA ∪ RA = Finset.univ := by
      simpa [LA, RA] using parity_union A
    have hpartB : GB.IsBipartiteWith (LB : Set _) (RB : Set _) := by
      simpa [GB, LB, RB] using (parity_bipartite B).symm
    have hcoverB : LB ∪ RB = Finset.univ := by
      have hu := parity_union B
      rw [Finset.union_comm] at hu
      simpa [LB, RB] using hu
    have hdegAfull : ∀ v ∈ LA, GA.degree v = 3 := by
      intro v hv
      have hp : cubeParity v.1 = false := by simpa [LA, paritySide] using hv
      rw [induced_degree_eq_neighbor_card]
      have heq : (hypercube 9).neighborFinset v.1 ∩ A =
          (hypercube 9).neighborFinset v.1 ∩ C := by
        ext y
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        constructor
        · intro hy
          exact ⟨hy.1, (Finset.filter_subset _ _) hy.2⟩
        · intro hy
          rcases hA_neighbor_cases v.1 v.property hy.2 hy.1 with hya | hyj
          · exact ⟨hy.1, hya⟩
          · exact (Bool.false_ne_true (hp.symm.trans hyj.2)).elim
      rw [heq, ← induced_degree_eq_neighbor_card C
        ⟨v.1, (Finset.filter_subset _ _) v.property⟩]
      exact hr.degree_eq _
    have hdegAother : ∀ v ∈ RA, GA.degree v = 2 ∨ GA.degree v = 3 := by
      intro v hv
      simpa [GA] using hAdeg v.1 v.property
    have hdegBfull : ∀ v ∈ LB, GB.degree v = 3 := by
      intro v hv
      have hp : cubeParity v.1 = true := by simpa [LB, paritySide] using hv
      rw [induced_degree_eq_neighbor_card]
      have heq : (hypercube 9).neighborFinset v.1 ∩ B =
          (hypercube 9).neighborFinset v.1 ∩ C := by
        ext y
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        constructor
        · intro hy
          exact ⟨hy.1, (Finset.filter_subset _ _) hy.2⟩
        · intro hy
          rcases hB_neighbor_cases v.1 v.property hy.2 hy.1 with hya | hyj
          · exact ⟨hy.1, hya⟩
          · exact (Bool.false_ne_true (hyj.2.symm.trans hp)).elim
      rw [heq, ← induced_degree_eq_neighbor_card C
        ⟨v.1, (Finset.filter_subset _ _) v.property⟩]
      exact hr.degree_eq _
    have hdegBother : ∀ v ∈ RB, GB.degree v = 2 ∨ GB.degree v = 3 := by
      intro v hv
      simpa [GB] using hBdeg v.1 v.property
    have hgA : (8 : ℕ∞) ≤ GA.egirth := by
      simpa [GA] using BalancedCubeGirth.eight_le_egirth A hbA
    have hgB : (8 : ℕ∞) ≤ GB.egirth := by
      simpa [GB] using BalancedCubeGirth.eight_le_egirth B hbB
    have hA_local (v : (A : Set Q9)) (hv : v ∈ RA) :
        GA.degree v +
            (if flip v.1 j ∈ C ∧ flip v.1 j ∉ A then 1 else 0) = 3 := by
      let N : Finset Q9 := (hypercube 9).neighborFinset v.1 ∩ C
      let I : Finset Q9 := (hypercube 9).neighborFinset v.1 ∩ A
      have hN : N.card = 3 := by
        rw [← induced_degree_eq_neighbor_card C
          ⟨v.1, (Finset.filter_subset _ _) v.property⟩]
        exact hr.degree_eq _
      have hsubI : I ⊆ N := by
        intro y hy
        simp only [I, N, Finset.mem_inter] at hy ⊢
        exact ⟨hy.1, (Finset.filter_subset _ _) hy.2⟩
      have hNsub : N ⊆ I ∪ {flip v.1 j} := by
        intro y hy
        simp only [N, Finset.mem_inter] at hy
        have hxy : (hypercube 9).Adj v.1 y :=
          ((hypercube 9).mem_neighborFinset v.1 y).mp hy.1
        rcases hA_neighbor_cases v.1 v.property hy.2 hxy with hya | hyj
        · have hyI : y ∈ I := by
            simp only [I, Finset.mem_inter]
            exact ⟨hy.1, hya⟩
          exact Finset.mem_union_left _ hyI
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hyj.1)
      have hdegI : GA.degree v = I.card := by
        rw [induced_degree_eq_neighbor_card]
      rw [hdegI]
      by_cases hc : flip v.1 j ∈ C ∧ flip v.1 j ∉ A
      · have hsN : flip v.1 j ∈ N := by
          simp [N, hc.1, flip_adj]
        have hUN : I ∪ {flip v.1 j} = N := by
          apply Finset.Subset.antisymm
          · intro y hy
            simp only [Finset.mem_union, Finset.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hsubI hy
            · exact hsN
          · exact hNsub
        have hdis : Disjoint I {flip v.1 j} :=
          Finset.disjoint_singleton_right.mpr (by
            intro hy
            exact hc.2 (Finset.mem_inter.mp hy).2)
        have hcardN : I.card + 1 = N.card := by
          rw [← hUN, Finset.card_union_of_disjoint hdis, Finset.card_singleton]
        simp [hc]
        omega
      · have hNI : N ⊆ I := by
          intro y hy
          simp only [N, Finset.mem_inter] at hy
          have hxy : (hypercube 9).Adj v.1 y :=
            ((hypercube 9).mem_neighborFinset v.1 y).mp hy.1
          rcases hA_neighbor_cases v.1 v.property hy.2 hxy with hya | hyj
          · have hyI : y ∈ I := by
              simp only [I, Finset.mem_inter]
              exact ⟨hy.1, hya⟩
            exact hyI
          · by_cases hfa : flip v.1 j ∈ A
            · have hyI : y ∈ I := by
                simp only [I, Finset.mem_inter]
                exact ⟨hy.1, by simpa [hyj.1] using hfa⟩
              exact hyI
            · exfalso
              apply hc
              exact ⟨by simpa [hyj.1] using hy.2, hfa⟩
        have hNIeq : N = I := Finset.Subset.antisymm hNI hsubI
        rw [← hNIeq]
        simp only [hc, if_false]
        exact hN
    have hB_local (v : (B : Set Q9)) (hv : v ∈ RB) :
        GB.degree v +
            (if flip v.1 j ∈ C ∧ flip v.1 j ∉ B then 1 else 0) = 3 := by
      let N : Finset Q9 := (hypercube 9).neighborFinset v.1 ∩ C
      let I : Finset Q9 := (hypercube 9).neighborFinset v.1 ∩ B
      have hN : N.card = 3 := by
        rw [← induced_degree_eq_neighbor_card C
          ⟨v.1, (Finset.filter_subset _ _) v.property⟩]
        exact hr.degree_eq _
      have hsubI : I ⊆ N := by
        intro y hy
        simp only [I, N, Finset.mem_inter] at hy ⊢
        exact ⟨hy.1, (Finset.filter_subset _ _) hy.2⟩
      have hNsub : N ⊆ I ∪ {flip v.1 j} := by
        intro y hy
        simp only [N, Finset.mem_inter] at hy
        have hxy : (hypercube 9).Adj v.1 y :=
          ((hypercube 9).mem_neighborFinset v.1 y).mp hy.1
        rcases hB_neighbor_cases v.1 v.property hy.2 hxy with hya | hyj
        · have hyI : y ∈ I := by
            simp only [I, Finset.mem_inter]
            exact ⟨hy.1, hya⟩
          exact Finset.mem_union_left _ hyI
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hyj.1)
      have hdegI : GB.degree v = I.card := by
        rw [induced_degree_eq_neighbor_card]
      rw [hdegI]
      by_cases hc : flip v.1 j ∈ C ∧ flip v.1 j ∉ B
      · have hsN : flip v.1 j ∈ N := by simp [N, hc.1, flip_adj]
        have hUN : I ∪ {flip v.1 j} = N := by
          apply Finset.Subset.antisymm
          · intro y hy
            simp only [Finset.mem_union, Finset.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hsubI hy
            · exact hsN
          · exact hNsub
        have hdis : Disjoint I {flip v.1 j} :=
          Finset.disjoint_singleton_right.mpr (by
            intro hy
            exact hc.2 (Finset.mem_inter.mp hy).2)
        have hcardN : I.card + 1 = N.card := by
          rw [← hUN, Finset.card_union_of_disjoint hdis, Finset.card_singleton]
        simp [hc]
        omega
      · have hNI : N ⊆ I := by
          intro y hy
          simp only [N, Finset.mem_inter] at hy
          have hxy : (hypercube 9).Adj v.1 y :=
            ((hypercube 9).mem_neighborFinset v.1 y).mp hy.1
          rcases hB_neighbor_cases v.1 v.property hy.2 hxy with hya | hyj
          · have hyI : y ∈ I := by
              simp only [I, Finset.mem_inter]
              exact ⟨hy.1, hya⟩
            exact hyI
          · by_cases hfa : flip v.1 j ∈ B
            · have hyI : y ∈ I := by
                simp only [I, Finset.mem_inter]
                exact ⟨hy.1, by simpa [hyj.1] using hfa⟩
              exact hyI
            · exfalso
              apply hc
              exact ⟨by simpa [hyj.1] using hy.2, hfa⟩
        have hNIeq : N = I := Finset.Subset.antisymm hNI hsubI
        rw [← hNIeq]
        simp only [hc, if_false]
        exact hN
    let BA : Finset (A : Set Q9) := RA.filter
      (fun v => flip v.1 j ∈ C ∧ flip v.1 j ∉ A)
    let BB : Finset (B : Set Q9) := RB.filter
      (fun v => flip v.1 j ∈ C ∧ flip v.1 j ∉ B)
    have hsumA := SimpleGraph.isBipartiteWith_sum_degrees_eq hpartA
    have hsumB := SimpleGraph.isBipartiteWith_sum_degrees_eq hpartB
    have hsumLA : (∑ v ∈ LA, GA.degree v) = 3 * LA.card := by
      rw [Finset.sum_congr rfl hdegAfull]
      simp [Nat.mul_comm]
    have hsumLB : (∑ v ∈ LB, GB.degree v) = 3 * LB.card := by
      rw [Finset.sum_congr rfl hdegBfull]
      simp [Nat.mul_comm]
    have hindA : (∑ v ∈ RA,
        (if flip v.1 j ∈ C ∧ flip v.1 j ∉ A then 1 else 0)) = BA.card := by
      simp [BA]
    have hindB : (∑ v ∈ RB,
        (if flip v.1 j ∈ C ∧ flip v.1 j ∉ B then 1 else 0)) = BB.card := by
      simp [BB]
    have hsumRA : (∑ v ∈ RA, GA.degree v) + BA.card = 3 * RA.card := by
      have hh := Finset.sum_congr rfl hA_local
      rw [Finset.sum_add_distrib, hindA] at hh
      simpa [Nat.mul_comm] using hh
    have hsumRB : (∑ v ∈ RB, GB.degree v) + BB.card = 3 * RB.card := by
      have hh := Finset.sum_congr rfl hB_local
      rw [Finset.sum_add_distrib, hindB] at hh
      simpa [Nat.mul_comm] using hh
    have hqA : 3 * LA.card + BA.card = 3 * RA.card := by omega
    have hqB : 3 * LB.card + BB.card = 3 * RB.card := by omega
    have hBA_nonempty : BA.Nonempty := by
      obtain ⟨x, hxA, hxc, hxnot⟩ := hAqpos
      have hrel := hstep' (Finset.filter_subset _ _ hxA) j hxc
      have hp : cubeParity x = true := by
        rcases hrel with ⟨_, hp, hval⟩ | ⟨_, hp, hval⟩ | hne
        · have hlow := hmin_le (flip x j) hxc
          have hx' := (Finset.mem_filter.mp hxA).2
          omega
        · exact hp
        · exact (hne.1 rfl).elim
      refine ⟨⟨x, hxA⟩, ?_⟩
      simp [BA, RA, paritySide, hp, hxc, hxnot]
    have hBB_nonempty : BB.Nonempty := by
      obtain ⟨x, hxB, hxc, hxnot⟩ := hBqpos
      have hrel := hstep' (Finset.filter_subset _ _ hxB) j hxc
      have hp : cubeParity x = false := by
        rcases hrel with ⟨_, hp, hval⟩ | ⟨_, hp, hval⟩ | hne
        · exact hp
        · have hhigh := hle_max (flip x j) hxc
          have hx' := (Finset.mem_filter.mp hxB).2
          omega
        · exact (hne.1 rfl).elim
      refine ⟨⟨x, hxB⟩, ?_⟩
      simp [BB, RB, paritySide, hp, hxc, hxnot]
    let KA : Finset Q9 := BA.image (fun v => kappa j v.1)
    let KB : Finset Q9 := BB.image (fun v => kappa j v.1)
    have hKA_card : KA.card = BA.card := by
      dsimp [KA]
      rw [Finset.card_image_iff.mpr]
      intro x hx y hy hxy
      apply Subtype.ext
      have hk := kappa_eq_or hxy
      rcases hk with hxy | hflip
      · exact hxy.symm
      · have hnot := (Finset.mem_filter.mp hx).2.2
        have hya := y.property
        exact (hnot (by simpa [hflip] using hya)).elim
    have hKB_card : KB.card = BB.card := by
      dsimp [KB]
      rw [Finset.card_image_iff.mpr]
      intro x hx y hy hxy
      apply Subtype.ext
      have hk := kappa_eq_or hxy
      rcases hk with hxy | hflip
      · exact hxy.symm
      · have hnot := (Finset.mem_filter.mp hx).2.2
        have hya := y.property
        exact (hnot (by simpa [hflip] using hya)).elim
    let E : Finset Q9 := C.filter (fun x => x j = false ∧ flip x j ∈ C)
    have hEcard : E.card = 9 := by
      have he := direction_edge_count (d := 3) C hr hb j
      have he' : 6 * E.card = 54 := by
        simpa [E, directionEdges, hcard] using he
      omega
    have hKA_sub : KA ⊆ E := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      have hvA := (Finset.mem_filter.mp hv).1
      have hcross := (Finset.mem_filter.mp hv).2
      have hxc : v.1 ∈ C := (Finset.filter_subset _ _) v.property
      by_cases hjbit : v.1 j = false
      · simp [E, kappa, hjbit, hxc, hcross.1, flip_adj]
      · simp [E, kappa, hjbit, hxc, hcross.1,
          BalancedCriticalSpectrum.flip_flip]
    have hKB_sub : KB ⊆ E := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      have hvB := (Finset.mem_filter.mp hv).1
      have hcross := (Finset.mem_filter.mp hv).2
      have hxc : v.1 ∈ C := (Finset.filter_subset _ _) v.property
      by_cases hjbit : v.1 j = false
      · simp [E, kappa, hjbit, hxc, hcross.1, flip_adj]
      · simp [E, kappa, hjbit, hxc, hcross.1,
          BalancedCriticalSpectrum.flip_flip]
    have hdisK : Disjoint KA KB := by
      apply Finset.disjoint_left.mpr
      intro y hyA hyB
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyA
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hyB
      have hk : kappa j x.1 = kappa j z.1 := hxy.trans hzy.symm
      have hor := kappa_eq_or hk
      rcases hor with hzx | hzx
      · have hax := x.property
        have hbz := z.property
        have hbx : x.1 ∈ B := by simpa [hzx] using hbz
        exact (Finset.disjoint_left.mp hABdisj hax hbx).elim
      · have hxcross := (Finset.mem_filter.mp hx).2.1
        have hnot := (Finset.mem_filter.mp hx).2.2
        have hxval := (Finset.mem_filter.mp x.property).2
        have hzval := (Finset.mem_filter.mp z.property).2
        have hxC : x.1 ∈ C := (Finset.filter_subset _ _ x.property)
        have hxp := hA_neighbor_cases x.1 x.property hxcross (flip_adj x.1 j)
        have hp : cubeParity x.1 = true := by
          rcases hxp with hya | ⟨_, hp⟩
          · exact (hnot hya).elim
          · exact hp
        have hrel := hstep' hxC j hxcross
        have hh : h z.1 = h x.1 + 1 := by
          rcases hrel with ⟨_, hp0, hh⟩ | ⟨_, hp1, hh⟩ | hn
          · exact (Bool.false_ne_true (hp0.symm.trans hp)).elim
          · simpa [hzx] using hh
          · exact (hn.1 rfl).elim
        rw [hzval, hxval] at hh
        omega
    have hqtotal : BA.card + BB.card ≤ 9 := by
      have hu := Finset.card_le_card (Finset.union_subset hKA_sub hKB_sub)
      have hu' := Finset.card_union_of_disjoint hdisK
      rw [hu', hKA_card, hKB_card, hEcard] at hu
      exact hu
    have hqApos : 0 < BA.card := Finset.card_pos.mpr hBA_nonempty
    have hqBpos : 0 < BB.card := Finset.card_pos.mpr hBB_nonempty
    have hq_cases : (BA.card = 3 ∧ BB.card = 3) ∨
        (BA.card = 3 ∧ BB.card = 6) ∨ (BA.card = 6 ∧ BB.card = 3) := by
      omega
    have hAcard : LA.card + RA.card = A.card := by
      have hd : Disjoint LA RA := by
        simpa only [Finset.disjoint_coe] using hpartA.disjoint
      rw [← Finset.card_union_of_disjoint hd, hcoverA]
      simp
    have hBcard : LB.card + RB.card = B.card := by
      have hd : Disjoint LB RB := by
        simpa only [Finset.disjoint_coe] using hpartB.disjoint
      rw [← Finset.card_union_of_disjoint hd, hcoverB]
      simp
    have hAlow : 2 * RA.card ≤ ∑ v ∈ RA, GA.degree v := by
      calc
        2 * RA.card = ∑ _v ∈ RA, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ RA, GA.degree v := by
          apply Finset.sum_le_sum
          intro v hv
          rcases hdegAother v hv with h2 | h3 <;> omega
    have hBlow : 2 * RB.card ≤ ∑ v ∈ RB, GB.degree v := by
      calc
        2 * RB.card = ∑ _v ∈ RB, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ RB, GB.degree v := by
          apply Finset.sum_le_sum
          intro v hv
          rcases hdegBother v hv with h2 | h3 <;> omega
    have hAq_cases : BA.card = 3 ∨ BA.card = 6 := by omega
    have hBq_cases : BB.card = 3 ∨ BB.card = 6 := by omega
    have hAlarge : 28 ≤ A.card := by
      rcases hAq_cases with hq3 | hq6
      · obtain ⟨hn, hd, hp⟩ := side_spectrum hpartA hdegAfull
          (by intro v hv; rcases hdegAother v hv with h2 | h3 <;> omega) hgA
        have hn0 : (degreeSlice GA RA 0).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hvR, hv0⟩ := Finset.mem_filter.mp hv
          rcases hdegAother v hvR with h2 | h3 <;> omega
        have hn1 : (degreeSlice GA RA 1).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hvR, hv1⟩ := Finset.mem_filter.mp hv
          rcases hdegAother v hvR with h2 | h3 <;> omega
        have hn2 : (degreeSlice GA RA 2).card = 3 := by omega
        have hn3 : (degreeSlice GA RA 3).card = LA.card - 2 := by omega
        have hRone : RA.card = LA.card + 1 := by omega
        have hpoly : 0 ≤ (LA.card : ℤ)^2 - 14 * LA.card + 12 := by
          have hp' := hp
          rw [hn2, hn3] at hp'
          have hRprod : LA.card * RA.card = LA.card * (LA.card + 1) :=
            congrArg (fun n => LA.card * n) hRone
          rw [hRprod] at hp'
          have hpZ : ((3 * LA.card + 4 * 3 + 12 * (LA.card - 2) : ℕ) : ℤ) ≤
              ((LA.card * (LA.card + 1) : ℕ) : ℤ) := by
            exact_mod_cast hp'
          push_cast at hpZ
          nlinarith
        have hL2 : 2 ≤ LA.card := by omega
        have hL14 : 14 ≤ LA.card := by
          by_contra hsmall
          have hL13 : LA.card ≤ 13 := by omega
          have hprod : ((LA.card : ℤ) - 1) * ((LA.card : ℤ) - 13) ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos <;> omega
          have : (LA.card : ℤ)^2 - 14 * LA.card + 12 ≤ -1 := by
            nlinarith
          omega
        have h29 : 29 ≤ A.card := by omega
        omega
      · have hRdiff : RA.card = LA.card + 2 := by omega
        have hgap := SixBoundarySideGap.six_boundary_side_gap A LA RA
          hpartA hcoverA
          (by simpa [GA] using hdegAfull)
          (by intro v hv; change GA.degree v ≤ 3
              rcases hdegAother v hv with h2 | h3 <;> omega)
          hgA hRdiff
        rcases hgap with h2 | h4 | h28
        · have : 2 * RA.card ≤ 3 * LA.card := by
            calc
              2 * RA.card ≤ ∑ v ∈ RA, GA.degree v := hAlow
              _ = ∑ v ∈ LA, GA.degree v := hsumA.symm
              _ = 3 * LA.card := hsumLA
          omega
        · have : 2 * RA.card ≤ 3 * LA.card := by
            calc
              2 * RA.card ≤ ∑ v ∈ RA, GA.degree v := hAlow
              _ = ∑ v ∈ LA, GA.degree v := hsumA.symm
              _ = 3 * LA.card := hsumLA
          omega
        · exact h28
    have hBlarge : 28 ≤ B.card := by
      rcases hBq_cases with hq3 | hq6
      · obtain ⟨hn, hd, hp⟩ := side_spectrum hpartB hdegBfull
          (by intro v hv; rcases hdegBother v hv with h2 | h3 <;> omega) hgB
        have hn0 : (degreeSlice GB RB 0).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hvR, hv0⟩ := Finset.mem_filter.mp hv
          rcases hdegBother v hvR with h2 | h3 <;> omega
        have hn1 : (degreeSlice GB RB 1).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hvR, hv1⟩ := Finset.mem_filter.mp hv
          rcases hdegBother v hvR with h2 | h3 <;> omega
        have hn2 : (degreeSlice GB RB 2).card = 3 := by omega
        have hn3 : (degreeSlice GB RB 3).card = LB.card - 2 := by omega
        have hRone : RB.card = LB.card + 1 := by omega
        have hpoly : 0 ≤ (LB.card : ℤ)^2 - 14 * LB.card + 12 := by
          have hp' := hp
          rw [hn2, hn3] at hp'
          have hRprod : LB.card * RB.card = LB.card * (LB.card + 1) :=
            congrArg (fun n => LB.card * n) hRone
          rw [hRprod] at hp'
          have hpZ : ((3 * LB.card + 4 * 3 + 12 * (LB.card - 2) : ℕ) : ℤ) ≤
              ((LB.card * (LB.card + 1) : ℕ) : ℤ) := by
            exact_mod_cast hp'
          push_cast at hpZ
          nlinarith
        have hL2 : 2 ≤ LB.card := by omega
        have hL14 : 14 ≤ LB.card := by
          by_contra hsmall
          have hL13 : LB.card ≤ 13 := by omega
          have hprod : ((LB.card : ℤ) - 1) * ((LB.card : ℤ) - 13) ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos <;> omega
          have : (LB.card : ℤ)^2 - 14 * LB.card + 12 ≤ -1 := by
            nlinarith
          omega
        have h29 : 29 ≤ B.card := by omega
        omega
      · have hRdiff : RB.card = LB.card + 2 := by omega
        have hgap := SixBoundarySideGap.six_boundary_side_gap B LB RB
          hpartB hcoverB
          (by simpa [GB] using hdegBfull)
          (by intro v hv; change GB.degree v ≤ 3
              rcases hdegBother v hv with h2 | h3 <;> omega)
          hgB hRdiff
        rcases hgap with h2 | h4 | h28
        · have : 2 * RB.card ≤ 3 * LB.card := by
            calc
              2 * RB.card ≤ ∑ v ∈ RB, GB.degree v := hBlow
              _ = ∑ v ∈ LB, GB.degree v := hsumB.symm
              _ = 3 * LB.card := hsumLB
          omega
        · have : 2 * RB.card ≤ 3 * LB.card := by
            calc
              2 * RB.card ≤ ∑ v ∈ RB, GB.degree v := hBlow
              _ = ∑ v ∈ LB, GB.degree v := hsumB.symm
              _ = 3 * LB.card := hsumLB
          omega
        · exact h28
    have hABcard : A.card + B.card ≤ 54 := by
      have hsubA : A ⊆ C := Finset.filter_subset _ _
      have hsubB : B ⊆ C := Finset.filter_subset _ _
      have hu := Finset.card_le_card (Finset.union_subset hsubA hsubB)
      rw [Finset.card_union_of_disjoint hABdisj, hcard] at hu
      exact hu
    omega
  intro x hx y hy
  change h x ≤ h y + 1
  have hxM := hle_max x hx
  have hym := hmin_le y hy
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.EightUniformHeightSpan
