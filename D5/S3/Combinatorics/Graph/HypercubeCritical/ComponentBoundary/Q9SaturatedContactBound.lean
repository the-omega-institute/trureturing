/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SaturatedContactBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SaturatedContactBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exterior mate incidences bound the crossing edges away from the common boundary. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9HighLeafPacking
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverPacking
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CommonBoundaryObstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedCollisionEnergyBound

/-! The mate count from `q9-high-leaf-packing.txt` and its distance-two consequence
from `q9-saturated-complement-projectors.txt`. -/

set_option autoImplicit false
set_option maxRecDepth 2048

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SaturatedContactBound

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_adj)
open BalancedCubeComponentBoundary (directions regular_directions exterior_even
  neighbor_card_add_le_six)
open Q9BoundaryEdgeTranslations (boundary)
open Q9MixedBoundaryCollisions (Separated)
open Q9EightfoldCoverPacking
  (eightfoldCoverEdges mem_eightfoldCoverEdges thirtyTwo_mul_card_eightfoldCoverEdges_le)
open Q9HighLeafPacking (highLeafDirections card_highLeafDirections_le_by_degree)
open Q9MixedCollisionEnergyBound (distanceTwoPairs)

open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private mem_directions directions_card flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private steps card_steps card_steps_symm card_steps_partition
  boundary_subset_complement card_filtered_product from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryEdgeTranslations
open private mem_highLeafDirections from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9HighLeafPacking
open private mem_boundary_iff distance_two_of_common_neighbor from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CommonBoundaryObstruction
open private mem_distanceTwoPairs from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedCollisionEnergyBound
open private diff diff_flip diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

local notation "flip" => BalancedCriticalSpectrum.flip

attribute [local instance] Classical.propDecidable

attribute [local irreducible] eightfoldCoverEdges

private theorem degree_le_nine (S : Finset (Q 9)) (x : Q 9) : (directions S x).card ≤ 9 := by
  simpa using Finset.card_le_univ (directions S x)

private def mateAxis (D : Finset (Q 9)) (y : Q 9) : Fin 9 :=
  if h : ∃ i, flip y i ∉ D ∧ ∀ j ≠ i, flip y j ∈ D then h.choose else 0

private theorem mateAxis_spec {D : Finset (Q 9)} {y : Q 9} (hy : (directions D y).card = 8) :
    flip y (mateAxis D y) ∉ D ∧ ∀ j ≠ mateAxis D y, flip y j ∈ D := by
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (directions D y))
  change _ + (directions D y).card = _ at hcard
  rw [hy, Finset.card_univ, Fintype.card_fin] at hcard
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (show (_ : ℕ) = 1 by omega :
    (Finset.univ \ directions D y).card = 1)
  have hmissing (j : Fin 9) : flip y j ∉ D ↔ j = i := by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_directions, Finset.mem_singleton]
      using Finset.ext_iff.mp hi j
  have hex : ∃ i, flip y i ∉ D ∧ ∀ j ≠ i, flip y j ∈ D :=
    ⟨i, (hmissing i).mpr rfl, fun j hj => by
      by_contra h
      exact hj ((hmissing j).mp h)⟩
  simpa only [mateAxis, dite_eq_left hex] using hex.choose_spec

private abbrev mate (D : Finset (Q 9)) (y : Q 9) : Q 9 := flip y (mateAxis D y)

attribute [local irreducible] mateAxis

private theorem mate_mem {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {y : Q 9} (hy : y ∈ (Finset.univ \ (C ∪ D)) \ boundary C)
    (h8 : (directions D y).card = 8) :
    mate D y ∈ (Finset.univ \ (C ∪ D)) \ boundary C := by
  have hyC : y ∉ C := fun hyC =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy).1).2 (Finset.mem_union_left _ hyC)
  obtain ⟨hxD, hcover⟩ := mateAxis_spec (D := D) (y := y) h8
  have hnone (j : Fin 9) : flip (mate D y) j ∉ C := by
    intro hj
    by_cases hji : j = mateAxis D y
    · exact hyC (by simpa only [hji, BalancedCriticalSpectrum.flip_flip] using hj)
    · have hadj := flip_adj (flip y j) (mateAxis D y)
      rw [flip_comm y j (mateAxis D y)] at hadj
      exact hsep.2 _ hj _ (hcover j hji) hadj.symm
  have hempty : directions C (mate D y) = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun j hj =>
      hnone j ((mem_directions C (mate D y) j).mp hj)
  have hxC : mate D y ∉ C := by
    intro hx
    have h := regular_directions C hrC hx
    simp [hempty] at h
  simp [boundary, hxC, hxD, hempty]

private theorem edge_mem_of_high_mate {D : Finset (Q 9)} {y : Q 9}
    (hyD : y ∉ D) (hy : (directions D y).card = 8) (hx : (directions D (mate D y)).card = 8) :
    ({y, mate D y} : Finset (Q 9)) ∈ eightfoldCoverEdges D := by
  obtain ⟨hxD, hycover⟩ := mateAxis_spec (D := D) (y := y) hy
  obtain ⟨_, hxcover⟩ := mateAxis_spec (D := D) (y := mate D y) hx
  have haxis : mateAxis D y = mateAxis D (mate D y) := by
    by_contra h
    exact hyD (by simpa only [BalancedCriticalSpectrum.flip_flip] using hxcover (mateAxis D y) h)
  exact mem_eightfoldCoverEdges.mpr
    ⟨y, mateAxis D y,
      ⟨hyD, hxD, fun j hj => ⟨hycover j hj, hxcover j (fun he => hj (he.trans haxis.symm))⟩⟩,
      rfl⟩

private theorem high_mate_fiber_le {D P : Finset (Q 9)} {x : Q 9}
    (hP : ∀ y ∈ P, y ∉ D) :
    ((P.filter fun y => (directions D y).card = 8).filter fun y =>
        (directions D (mate D y)).card ≠ 8 ∧ mate D y = x).card ≤
      (highLeafDirections D x).card := by
  apply Finset.card_le_card_of_injOn (mateAxis D)
  · intro y hy
    obtain ⟨hy, _, hmate⟩ := Finset.mem_filter.mp hy
    have h8 := (Finset.mem_filter.mp hy).2
    obtain ⟨_, hycover⟩ := mateAxis_spec (D := D) (y := y) h8
    have hback : flip x (mateAxis D y) = y := by
      rw [← hmate, BalancedCriticalSpectrum.flip_flip]
    apply mem_highLeafDirections.mpr
    rw [hback]
    exact ⟨hP y (Finset.mem_filter.mp hy).1, hycover⟩
  · intro y hy z hz he
    have hyx := (Finset.mem_filter.mp hy).2.2
    have hzx := (Finset.mem_filter.mp hz).2.2
    calc
      y = flip x (mateAxis D y) := by rw [← hyx, BalancedCriticalSpectrum.flip_flip]
      _ = flip x (mateAxis D z) := by rw [he]
      _ = z := by rw [← hzx, BalancedCriticalSpectrum.flip_flip]

private theorem sum_exterior_degrees {D P : Finset (Q 9)}
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbD : IsBalanced D) (hP : ∀ x ∈ P, x ∉ D) (f : ℕ → ℕ) :
    let r := fun k => (P.filter fun x => (directions D x).card = k).card
    (∑ x ∈ P, f ((directions D x).card)) =
      r 0 * f 0 + r 2 * f 2 + r 4 * f 4 + r 6 * f 6 + r 8 * f 8 := by
  let degrees : Finset ℕ := {0, 2, 4, 6, 8}
  have hmaps : ∀ x ∈ P, (directions D x).card ∈ degrees := by
    intro x hx
    have hle := degree_le_nine D x
    obtain ⟨k, hk⟩ := exterior_even D hrD hbD x (hP x hx)
    simp only [degrees, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps f]
  simp [degrees, Finset.sum_insert, add_assoc, Nat.mul_comm]

/-- The degree-eight leaves outside the first boundary are bounded by two per unordered
eightfold edge and by the degree-dependent capacities of their other mates. -/
theorem high_leaf_mate_bound {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbD : IsBalanced D) :
    let P := (Finset.univ \ (C ∪ D)) \ boundary C
    let r := fun k => (P.filter fun x => (directions D x).card = k).card
    r 8 ≤ 2 * (eightfoldCoverEdges D).card + 3 * r 0 + 2 * r 2 + r 4 + r 6 := by
  dsimp only
  let P := (Finset.univ \ (C ∪ D)) \ boundary C
  let H := P.filter fun y => (directions D y).card = 8
  let highMate := fun y => (directions D (mate D y)).card = 8
  let capacity := fun k : ℕ => if k = 8 then 0 else if k = 0 then 3 else if k = 2 then 2 else 1
  have hP : ∀ x ∈ P, x ∉ D := fun x hx hxD =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 (Finset.mem_union_right _ hxD)
  have hhigh : (H.filter highMate).card ≤ 2 * (eightfoldCoverEdges D).card := by
    calc
      _ ≤ ((eightfoldCoverEdges D).biUnion id).card := by
        apply Finset.card_le_card
        intro y hy
        obtain ⟨hyH, hyMate⟩ := Finset.mem_filter.mp hy
        obtain ⟨hyP, hy8⟩ := Finset.mem_filter.mp hyH
        exact Finset.mem_biUnion.mpr
          ⟨{y, mate D y}, edge_mem_of_high_mate (hP y hyP) hy8 hyMate, by simp⟩
      _ ≤ ∑ e ∈ eightfoldCoverEdges D, e.card := Finset.card_biUnion_le
      _ = 2 * (eightfoldCoverEdges D).card := by
        rw [Finset.sum_const_nat (m := 2), Nat.mul_comm]
        intro e he
        obtain ⟨y, i, _, rfl⟩ := mem_eightfoldCoverEdges.mp he
        exact Finset.card_pair (flip_adj y i).ne
  have hlow : (H.filter fun y => ¬ highMate y).card ≤
      ∑ x ∈ P, capacity (directions D x).card := by
    have hmaps : ∀ y ∈ H.filter (fun y => ¬ highMate y), mate D y ∈ P := by
      intro y hy
      obtain ⟨hyP, hy8⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hy).1
      exact mate_mem hsep hrC hyP hy8
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_le_sum
    intro x hx
    rw [Finset.filter_filter]
    by_cases h8 : (directions D x).card = 8
    · have hempty :
          (H.filter fun y => (fun y => ¬ highMate y) y ∧ mate D y = x) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨_, hy8, he⟩ := Finset.mem_filter.mp hy
        exact hy8 (by simpa only [highMate, he] using h8)
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · obtain ⟨sigma, hs⟩ := hbD
      exact (high_mate_fiber_le (x := x) hP).trans
        (by simpa only [capacity, ite_eq_right h8] using
          card_highLeafDirections_le_by_degree hrD hs (hP x hx))
  have hclasses := sum_exterior_degrees hrD hbD hP capacity
  norm_num only [capacity, Nat.mul_comm] at hclasses
  simp only [ite_false, ite_true, zero_mul, one_mul, add_zero] at hclasses
  have hsplit := Finset.card_filter_add_card_filter_not (s := H) highMate
  let r := fun k => (P.filter fun x => (directions D x).card = k).card
  change (∑ x ∈ P, capacity ((directions D x).card)) = 3 * r 0 + 2 * r 2 + r 4 + r 6 at hclasses
  change H.card ≤ 2 * (eightfoldCoverEdges D).card + 3 * r 0 + 2 * r 2 + r 4 + r 6
  omega

private theorem sum_outside_boundary_le {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbD : IsBalanced D) :
    let P := (Finset.univ \ (C ∪ D)) \ boundary C
    (∑ x ∈ P, (directions D x).card) ≤ 7 * P.card + 2 * (eightfoldCoverEdges D).card := by
  dsimp only
  let P := (Finset.univ \ (C ∪ D)) \ boundary C
  have hP : ∀ x ∈ P, x ∉ D := fun x hx hxD =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 (Finset.mem_union_right _ hxD)
  have hmates := high_leaf_mate_bound hsep hrC hrD hbD
  dsimp only at hmates
  have hsum := sum_exterior_degrees hrD hbD hP id
  have hcard := sum_exterior_degrees hrD hbD hP (fun _ => 1)
  simp only [id_eq, Nat.mul_zero, zero_add] at hsum
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one] at hcard
  change (∑ x ∈ P, (directions D x).card) ≤ 7 * P.card + 2 * (eightfoldCoverEdges D).card
  let r := fun k => (P.filter fun x => (directions D x).card = k).card
  change r 8 ≤ 2 * (eightfoldCoverEdges D).card + 3 * r 0 + 2 * r 2 + r 4 + r 6 at hmates
  change (∑ x ∈ P, (directions D x).card) = r 2 * 2 + r 4 * 4 + r 6 * 6 + r 8 * 8 at hsum
  change P.card = r 0 + r 2 + r 4 + r 6 + r 8 at hcard
  omega

/-- In a saturated pair, the contact sum retains the actual number of neighbors in
the second support at each common exterior vertex. -/
theorem saturated_contact_sum_bound {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbD : IsBalanced D) (hsize : C.card + D.card = 258) :
    6 * D.card ≤ (∑ x ∈ boundary C ∩ boundary D, (directions D x).card) +
      7 * (254 - (boundary C).card) + 2 * (eightfoldCoverEdges D).card := by
  let T : Finset (Q 9) := Finset.univ \ (C ∪ D)
  have hT : T.card = 254 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hsep.1, hsize, Finset.card_univ]
    norm_num [Q, Sensitivity.Q, Fintype.card_fun]
  have hBC : boundary C ⊆ T := by
    apply boundary_subset_complement
    intro c hc d hd
    exact hsep.2 c hc d ((Finset.mem_union.mp (Finset.mem_sdiff.mp hd).1).resolve_left
      (Finset.mem_sdiff.mp hd).2)
  have hD : (steps D (C ∪ D)).card = 3 * D.card := by
    rw [card_steps, Nat.mul_comm, Finset.sum_const_nat]
    intro d hd
    have heq : directions (C ∪ D) d = directions D d := by
      ext i
      simp only [mem_directions, Finset.mem_union]
      exact or_iff_right (fun hc => hsep.2 _ hc _ hd (flip_adj d i).symm)
    rw [heq, regular_directions D hrD hd]
  have hpart := card_steps_partition D (C ∪ D)
  have hcut : (∑ x ∈ T, (directions D x).card) = 6 * D.card := by
    rw [← card_steps, card_steps_symm T D]
    change (steps D (Finset.univ \ (C ∪ D))).card = _
    omega
  have hsplit :
      (∑ x ∈ T \ boundary C, (directions D x).card) +
        (∑ x ∈ boundary C, (directions D x).card) =
        ∑ x ∈ T, (directions D x).card :=
    Finset.sum_sdiff hBC
  have hcontact :
      (∑ x ∈ boundary C ∩ boundary D, (directions D x).card) =
        ∑ x ∈ boundary C, (directions D x).card := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro x hx hxK
    have hxD : x ∉ D := fun hd =>
      (Finset.mem_sdiff.mp (hBC hx)).2 (Finset.mem_union_right _ hd)
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro h
    apply hxK
    refine Finset.mem_inter.mpr ⟨hx, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxD, h⟩
  have hout := sum_outside_boundary_le hsep hrC hrD hbD
  change (∑ x ∈ T \ boundary C, (directions D x).card) ≤
    7 * (T \ boundary C).card + 2 * (eightfoldCoverEdges D).card at hout
  rw [Finset.card_sdiff_of_subset hBC, hT] at hout
  omega

private theorem two_le_degree_of_boundary {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) {x : Q 9} (hx : x ∈ boundary S) : 2 ≤ (directions S x).card := by
  obtain ⟨hxS, hnonempty⟩ := (Finset.mem_filter.mp hx).2
  have hpos := Finset.card_pos.mpr hnonempty
  obtain ⟨k, hk⟩ := exterior_even S hr hb x hxS
  omega

/-- At a common exterior vertex, balance and the six-neighbor bound leave at most
four neighbors in the second support. -/
theorem saturated_contact_card_bound {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hsize : C.card + D.card = 258) :
    6 * D.card ≤ 4 * (boundary C ∩ boundary D).card +
      7 * (254 - (boundary C).card) + 2 * (eightfoldCoverEdges D).card := by
  have hsum : (∑ x ∈ boundary C ∩ boundary D, (directions D x).card) ≤
      4 * (boundary C ∩ boundary D).card := by
    rw [Nat.mul_comm 4, ← Finset.sum_const_nat (fun _ _ => rfl)]
    apply Finset.sum_le_sum
    intro x hx
    obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hx
    have hC := two_le_degree_of_boundary hrC hbC hxC
    have hD := two_le_degree_of_boundary hrD hbD hxD
    have hsix := neighbor_card_add_le_six C D hrC hrD hbC hbD hsep.1 hsep.2 x
      (mem_boundary_iff.mp hxC).1 (mem_boundary_iff.mp hxD).1
      (by rw [← directions_card]; omega) (by rw [← directions_card]; omega)
    rw [← directions_card C x, ← directions_card D x] at hsix
    omega
  have h := saturated_contact_sum_bound hsep hrC hrD hbD hsize
  omega

/-- Each distance-two cross pair has two common neighbors, both in the common boundary. -/
theorem two_mul_distanceTwoPairs_card {C D : Finset (Q 9)} (hsep : Separated C D) :
    2 * (distanceTwoPairs C D).card =
      ∑ x ∈ boundary C ∩ boundary D, (directions C x).card * (directions D x).card := by
  let K := boundary C ∩ boundary D
  let P := distanceTwoPairs C D
  let I := (K ×ˢ (C ×ˢ D)).filter (fun w =>
    (hypercube 9).Adj w.1 w.2.1 ∧ (hypercube 9).Adj w.1 w.2.2)
  have hbyVertex : I.card = ∑ x ∈ K, (directions C x).card * (directions D x).card := by
    dsimp only [I]
    rw [← Finset.product_eq_sprod (s := K) (t := C ×ˢ D), card_filtered_product]
    apply Finset.sum_congr rfl
    intro x _
    have hfilter :
        ((C ×ˢ D).filter
          (fun p => (hypercube 9).Adj x p.1 ∧ (hypercube 9).Adj x p.2)) =
          (C.filter ((hypercube 9).Adj x)) ×ˢ (D.filter ((hypercube 9).Adj x)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      tauto
    rw [hfilter, Finset.card_product, ← directions_card, ← directions_card]
  have hmaps : ∀ w ∈ I, w.2 ∈ P := by
    rintro ⟨x, c, d⟩ hw
    obtain ⟨hw, hxc, hxd⟩ := Finset.mem_filter.mp hw
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp (Finset.mem_product.mp hw).2
    have hcd : c ≠ d := fun h => Finset.disjoint_left.mp hsep.1 hc (h ▸ hd)
    exact mem_distanceTwoPairs.mpr
      ⟨hc, hd, distance_two_of_common_neighbor hcd hxc.symm hxd.symm⟩
  have hbyPair : I.card = 2 * P.card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.mul_comm 2]
    apply Finset.sum_const_nat
    intro p hp
    obtain ⟨hc, hd, hdist⟩ := mem_distanceTwoPairs.mp hp
    have hne : p.1 ≠ p.2 := fun h => Finset.disjoint_left.mp hsep.1 hc (h ▸ hd)
    have hdiff : (diff p.1 p.2).card = 2 := hdist
    have hfiber : (I.filter fun w => w.2 = p) =
        ((diff p.1 p.2).image (flip p.1)) ×ˢ {p} := by
      ext ⟨x, q⟩
      constructor
      · intro h
        obtain ⟨hw, hq⟩ := Finset.mem_filter.mp h
        change q = p at hq
        subst q
        obtain ⟨_, hxc, hxd⟩ := Finset.mem_filter.mp hw
        obtain ⟨i, hi⟩ := adjacent_exists_flip hxc.symm
        have hadj : (hypercube 9).Adj (flip p.1 i) p.2 := by
          rw [← hi]
          exact hxd
        exact Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨i, (diff_of_adj_flip hne i hadj).1, hi.symm⟩,
            Finset.mem_singleton_self _⟩
      · intro h
        obtain ⟨hx, hq⟩ := Finset.mem_product.mp h
        have heq : q = p := Finset.mem_singleton.mp hq
        subst q
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        have hxc := flip_adj p.1 i
        have hxd : (hypercube 9).Adj (flip p.1 i) p.2 := by
          change (diff (flip p.1 i) p.2).card = 1
          rw [diff_flip, ite_eq_left hi, Finset.card_erase_of_mem hi, hdiff]
        have hxC : flip p.1 i ∉ C := fun hx => hsep.2 _ hx _ hd hxd
        have hxD : flip p.1 i ∉ D := fun hx => hsep.2 _ hc _ hx hxc
        have hxK : flip p.1 i ∈ K := Finset.mem_inter.mpr
          ⟨mem_boundary_iff.mpr ⟨hxC, _, hc, hxc⟩,
            mem_boundary_iff.mpr ⟨hxD, _, hd, hxd.symm⟩⟩
        have hprod : (flip p.1 i, p) ∈ K ×ˢ (C ×ˢ D) :=
          Finset.mem_product.mpr ⟨hxK, Finset.mem_product.mpr ⟨hc, hd⟩⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hprod, hxc.symm, hxd⟩, rfl⟩
    rw [hfiber, Finset.card_product, Finset.card_singleton, Nat.mul_one,
      Finset.card_image_of_injective _ (flip_injective p.1), hdiff]
  exact hbyPair.symm.trans hbyVertex

/-- The common exterior contact sum gives a lower bound for the distance-two pair count. -/
theorem sum_contact_le_distanceTwoPairs_card {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) :
    (∑ x ∈ boundary C ∩ boundary D, (directions D x).card) ≤ (distanceTwoPairs C D).card := by
  have hdouble : 2 * (∑ x ∈ boundary C ∩ boundary D, (directions D x).card) ≤
      ∑ x ∈ boundary C ∩ boundary D, (directions C x).card * (directions D x).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun _ hx => Nat.mul_le_mul_right _
      (two_le_degree_of_boundary hrC hbC (Finset.mem_inter.mp hx).1)
  rw [← two_mul_distanceTwoPairs_card hsep] at hdouble
  omega

/-- At the 72/186 stratum the contact bound gives 322 distance-two cross pairs when
the 72-vertex support has at least 142 exterior neighbors. -/
theorem distanceTwoPairs_card_ge_322 {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hc : C.card = 72) (hd : D.card = 186) (hboundary : 142 ≤ (boundary C).card) :
    322 ≤ (distanceTwoPairs C D).card := by
  have hcontact := saturated_contact_sum_bound hsep hrC hrD hbD (by omega)
  have hpack := thirtyTwo_mul_card_eightfoldCoverEdges_le hrD hbD
  have hpairs := sum_contact_le_distanceTwoPairs_card hsep hrC hbC
  omega

#print axioms high_leaf_mate_bound
#print axioms saturated_contact_sum_bound
#print axioms saturated_contact_card_bound
#print axioms two_mul_distanceTwoPairs_card
#print axioms sum_contact_le_distanceTwoPairs_card
#print axioms distanceTwoPairs_card_ge_322

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SaturatedContactBound
