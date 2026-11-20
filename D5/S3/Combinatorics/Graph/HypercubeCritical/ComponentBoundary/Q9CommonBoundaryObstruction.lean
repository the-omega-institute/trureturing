/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Large balanced cubic supports share exterior neighbors. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeClosedNeighborhoodRecurrence
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryEdgeTranslations
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinPairedCertificate

/-! Folding each parity class through one coordinate gives separate lower bounds
for the two parity classes of the exterior boundary. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CommonBoundaryObstruction

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count flip_adj)
open BalancedCubeComponentBoundary (directions regular_directions exterior_even)
open CubeClosedNeighborhoodRecurrence (closedNeighborhood half minHalfSize
  q8_closedNeighborhood_card_ge)
open Q9BoundaryEdgeTranslations (boundary)
open Q9ParityFoldedBoundary (parity parityPart dropCoordinate cubic_parityPart_card
  card_image_dropCoordinate coordinate_half_parity_bounds
  ten_le_coordinate_half_parity_of_no_twenty_half card_projected_parity_half
  card_neighbor_eq_card_closed_neighbor_image)
open private parity_eq_not_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private directions_card mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary


open private diff diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

attribute [local instance] Classical.propDecidable

private theorem mem_boundary_iff {C : Finset (Q 9)} {z : Q 9} :
    z ∈ boundary C ↔ z ∉ C ∧ ∃ x ∈ C, (hypercube 9).Adj x z := by
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hz, i, hi⟩
    exact ⟨hz, _, (mem_directions C z i).mp hi, (flip_adj z i).symm⟩
  · rintro ⟨hz, x, hx, hzx⟩
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hzx.symm
    exact ⟨hz, i, (mem_directions C z i).mpr hx⟩

/-- A large balanced cubic support has at least 130 exterior neighbors if its
first-coordinate halves have size different from 20 at order 72. -/
theorem boundary_card_ge_130_of_no_twenty_half {C : Finset (Q 9)}
    (hmin : 72 ≤ C.card) (hmax : C.card ≤ 186)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (h20 : C.card = 72 → ∀ b : Bool, (C.filter (fun x => x 0 = b)).card ≠ 20) :
    130 ≤ (boundary C).card := by
  classical
  let m := directionEdges C 0
  have hC : C.card = 6 * m := (direction_edge_count (d := 3) C hr hb 0).symm
  let N (p : Bool) : Finset (Q 9) :=
    Finset.univ.filter (fun z => ∃ x ∈ parityPart C p, (hypercube 9).Adj x z)
  have hpar (p : Bool) {z : Q 9} (hz : z ∈ N p) : parity z = !p := by
    obtain ⟨x, hx, hxz⟩ := (Finset.mem_filter.mp hz).2
    rw [parity_eq_not_of_adj hxz, (Finset.mem_filter.mp hx).2]
  have hN (p : Bool) : 3 * m + 65 ≤ (N p).card := by
    let A := parityPart C p
    let S := A.image (dropCoordinate (8 : Fin 9))
    have hA : ∀ x ∈ A, parity x = p := fun _ hx => (Finset.mem_filter.mp hx).2
    have hS : S.card = 3 * m := by
      change (A.image (dropCoordinate (8 : Fin 9))).card = _
      rw [card_image_dropCoordinate _ p A hA, cubic_parityPart_card hC hr]
    have hhalf (b : Bool) : minHalfSize m ≤ (half b S).card := by
      have hproj :
          half b S = (S.filter (fun x => x 0 = b)).image (Fin.tail (α := fun _ => Bool)) := by
        ext v
        simp only [half, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hv
          exact ⟨Fin.cons b v, ⟨hv, Fin.cons_zero _ _⟩, Fin.tail_cons _ _⟩
        · rintro ⟨x, ⟨hx, hxb⟩, rfl⟩
          rw [← hxb, Fin.cons_self_tail]
          exact hx
      have hinj : Set.InjOn (Fin.tail (α := fun _ : Fin 8 => Bool))
          (↑(S.filter (fun x => x 0 = b)) : Set (Q 8)) := by
        intro x hx y hy hxy
        have hxb := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        have hyb := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
        rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hxb, hyb, hxy]
      rw [hproj, Finset.card_image_of_injOn hinj]
      change minHalfSize m ≤
        (((parityPart C p).image (dropCoordinate (8 : Fin 9))).filter (fun x => x 0 = b)).card
      rw [card_projected_parity_half, show (8 : Fin 9).succAbove (0 : Fin 8) = 0 by decide]
      obtain ⟨hbound, _, h13⟩ := coordinate_half_parity_bounds hC hr hb 0 b p
      by_cases hm12 : m = 12
      · have h72 : C.card = 72 := by omega
        simpa [minHalfSize, hm12] using
          ten_le_coordinate_half_parity_of_no_twenty_half h72 hr hb 0 b p (h20 h72 b)
      by_cases hm13 : m = 13
      · simpa [minHalfSize, hm13, hm12] using h13 hm13
      simp only [minHalfSize, hm12, hm13, ite_false]
      have hceil (n : ℕ) (hn : 2 * m ≤ 3 * n) : (2 * m + 2) / 3 ≤ n := by omega
      exact hceil _ hbound
    have hbound := q8_closedNeighborhood_card_ge S (by omega) (by omega) hS
      (hhalf false) (hhalf true)
    change 3 * m + 65 ≤
      (Finset.univ.filter (fun z => ∃ x ∈ A, (hypercube 9).Adj x z)).card
    rw [card_neighbor_eq_card_closed_neighbor_image _ p A hA]
    have hfold : (Finset.univ.filter (fun v => ∃ u ∈ S, u = v ∨ (hypercube 8).Adj u v)) =
        closedNeighborhood S := by
      ext v
      simp only [closedNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]
      apply exists_congr
      intro u
      apply and_congr_right
      intro _
      change (u = v ∨ hammingDist u v = 1) ↔ hammingDist v u ≤ 1
      rw [hammingDist_comm v u, ← hammingDist_eq_zero]
      omega
    exact hfold.symm ▸ hbound
  have hinside (p : Bool) : N p ∩ C = parityPart C (!p) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzN, hzC⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_filter.mpr ⟨hzC, hpar p hzN⟩
    · intro hz
      obtain ⟨hzC, hzp⟩ := Finset.mem_filter.mp hz
      have hcard := regular_directions C hr hzC
      rw [directions_card] at hcard
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (hcard.symm ▸ (by decide : 0 < 3))
      obtain ⟨hxC, hzx⟩ := Finset.mem_filter.mp hx
      have hxp : parity x = p := by rw [parity_eq_not_of_adj hzx, hzp, Bool.not_not]
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Finset.mem_filter.mpr ⟨hxC, hxp⟩,
          hzx.symm⟩, hzC⟩
  have hExt (p : Bool) : 65 ≤ (N p \ C).card := by
    have hdiff : N p \ C = N p \ (N p ∩ C) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [hdiff, Finset.card_sdiff_of_subset Finset.inter_subset_left, hinside,
      cubic_parityPart_card hC hr]
    have := hN p
    omega
  have hdisj : Disjoint (N false \ C) (N true \ C) := by
    apply Finset.disjoint_left.mpr
    intro z hzF hzT
    have hpF := hpar false (Finset.mem_sdiff.mp hzF).1
    have hpT := hpar true (Finset.mem_sdiff.mp hzT).1
    simp_all
  have hunion : boundary C = (N false \ C) ∪ (N true \ C) := by
    ext z
    simp only [mem_boundary_iff, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hz, x, hx, hxz⟩
      cases hp : parity x
      · exact Or.inl
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Finset.mem_filter.mpr ⟨hx, hp⟩, hxz⟩, hz⟩
      · exact Or.inr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Finset.mem_filter.mpr ⟨hx, hp⟩, hxz⟩, hz⟩
    · rintro (⟨h, hz⟩ | ⟨h, hz⟩) <;>
        obtain ⟨x, hx, hxz⟩ := (Finset.mem_filter.mp h).2 <;>
        exact ⟨hz, x, (Finset.mem_filter.mp hx).1, hxz⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  exact Nat.add_le_add (hExt false) (hExt true)

/-- A closed balanced cubic support of order between 72 and 186 in a subcubic
258-point set has at least 130 exterior neighbors. -/
theorem boundary_card_ge_130 {U C : Finset (Q 9)} (hU : U.card = 258)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3)
    (hCU : C ⊆ U) (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hmin : 72 ≤ C.card) (hmax : C.card ≤ 186) :
    130 ≤ (boundary C).card :=
  boundary_card_ge_130_of_no_twenty_half hmin hmax hr hb
    (fun h72 b hsize =>
      Q9ThinPairedCertificate.no_thin_component_of_extension
        hU h72 hr hb b hsize hCU hclosed hdeg)

private theorem common_boundary_card_of_bounds {U C D : Finset (Q 9)}
    (hU : U.card = 258)
    (hclosedC : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hclosedD : ∀ x ∈ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ D)
    (hC : 130 ≤ (boundary C).card) (hD : 130 ≤ (boundary D).card) :
    6 ≤ (boundary C ∩ boundary D).card := by
  classical
  have hsub {S : Finset (Q 9)}
      (hclosed : ∀ x ∈ S, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ S) :
      boundary S ⊆ Finset.univ \ U := by
    intro z hz
    obtain ⟨hzS, x, hx, hxz⟩ := mem_boundary_iff.mp hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hzU => hzS (hclosed x hx z hzU hxz)⟩
  have hcap : (Finset.univ \ U).card = 254 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ,
      Sensitivity.Q.card, hU]
    decide
  have h := Finset.card_le_card (Finset.union_subset (hsub hclosedC) (hsub hclosedD))
  rw [hcap] at h
  have := Finset.card_union_add_card_inter (boundary C) (boundary D)
  omega

/-- Two disjoint large closed balanced cubic supports in a subcubic 258-point
set share at least six exterior neighbors. -/
theorem common_boundary_card_ge_6 {U C D : Finset (Q 9)} (hU : U.card = 258)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3)
    (hCU : C ⊆ U) (hDU : D ⊆ U) (hdisj : Disjoint C D)
    (hclosedC : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hclosedD : ∀ x ∈ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hminC : 72 ≤ C.card) (hminD : 72 ≤ D.card) :
    6 ≤ (boundary C ∩ boundary D).card := by
  have h := Finset.card_le_card (Finset.union_subset hCU hDU)
  rw [Finset.card_union_of_disjoint hdisj, hU] at h
  exact common_boundary_card_of_bounds hU hclosedC hclosedD
    (boundary_card_ge_130 hU hdeg hCU hclosedC hrC hbC hminC (by omega))
    (boundary_card_ge_130 hU hdeg hDU hclosedD hrD hbD hminD (by omega))

private theorem distance_two_of_common_neighbor {x y z : Q 9} (hne : x ≠ y)
    (hx : (hypercube 9).Adj x z) (hy : (hypercube 9).Adj y z) :
    hammingDist x y = 2 := by
  obtain ⟨i, rfl⟩ := adjacent_exists_flip hx
  exact (diff_of_adj_flip hne i hy.symm).2

/-- Two disjoint large closed balanced cubic supports in a subcubic 258-point
set have a pair of vertices at Hamming distance two. -/
theorem exists_distance_two_pair {U C D : Finset (Q 9)} (hU : U.card = 258)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3)
    (hCU : C ⊆ U) (hDU : D ⊆ U) (hdisj : Disjoint C D)
    (hclosedC : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hclosedD : ∀ x ∈ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hminC : 72 ≤ C.card) (hminD : 72 ≤ D.card) :
    ∃ x ∈ C, ∃ y ∈ D, hammingDist x y = 2 := by
  have hcard := common_boundary_card_ge_6 hU hdeg hCU hDU hdisj
    hclosedC hclosedD hrC hrD hbC hbD hminC hminD
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (boundary C ∩ boundary D).card by omega)
  obtain ⟨hzC, hzD⟩ := Finset.mem_inter.mp hz
  obtain ⟨_, x, hx, hxz⟩ := mem_boundary_iff.mp hzC
  obtain ⟨_, y, hy, hyz⟩ := mem_boundary_iff.mp hzD
  exact ⟨x, hx, y, hy, distance_two_of_common_neighbor
    (fun hxy => Finset.disjoint_left.mp hdisj hx (hxy ▸ hy))
    hxz hyz⟩

/-- Each common exterior neighbor gives at least four incidences with cross
pairs, and a cross pair has at most two common neighbors. -/
theorem distance_two_pairs_card_ge_12 {U C D : Finset (Q 9)} (hU : U.card = 258)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3)
    (hCU : C ⊆ U) (hDU : D ⊆ U) (hdisj : Disjoint C D)
    (hclosedC : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hclosedD : ∀ x ∈ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hminC : 72 ≤ C.card) (hminD : 72 ≤ D.card) :
    12 ≤ ((C.product D).filter (fun p => hammingDist p.1 p.2 = 2)).card := by
  classical
  let B := boundary C ∩ boundary D
  let P := (C.product D).filter (fun p => hammingDist p.1 p.2 = 2)
  let I := (B.product (C.product D)).filter (fun w =>
    (hypercube 9).Adj w.1 w.2.1 ∧ (hypercube 9).Adj w.1 w.2.2)
  have hB : 6 ≤ B.card := common_boundary_card_ge_6 hU hdeg hCU hDU hdisj
    hclosedC hclosedD hrC hrD hbC hbD hminC hminD
  have hdegree {S : Finset (Q 9)}
      (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
      (hb : IsBalanced S) {z : Q 9} (hz : z ∈ boundary S) :
      2 ≤ (S.filter ((hypercube 9).Adj z)).card := by
    obtain ⟨hzS, hn⟩ := (Finset.mem_filter.mp hz).2
    have hpos : 0 < (directions S z).card := Finset.card_pos.mpr hn
    obtain ⟨k, hk⟩ := exterior_even S hr hb z hzS
    have htwo : 2 ≤ (directions S z).card := by omega
    rw [directions_card] at htwo
    exact htwo
  have hlow : 4 * B.card ≤ I.card := by
    have hsum : 4 * B.card = ∑ _z ∈ B, (4 : ℕ) := by simp [Nat.mul_comm]
    rw [hsum, Finset.card_eq_sum_card_fiberwise (s := I) (f := Prod.fst) (t := B)
      (fun _ hw => (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1)]
    apply Finset.sum_le_sum
    intro z hz
    obtain ⟨hzC, hzD⟩ := Finset.mem_inter.mp hz
    have hfiber : (I.filter (fun w => w.1 = z)) =
        ({z} : Finset (Q 9)).product
          ((C.filter ((hypercube 9).Adj z)).product (D.filter ((hypercube 9).Adj z))) := by
      ext ⟨v, x, y⟩
      by_cases hv : v = z
      · subst v
        simp [I, hz, and_assoc, and_left_comm, and_comm]
      · simp [I, hv, Ne.symm hv]
    rw [hfiber]
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, one_mul]
    exact Nat.mul_le_mul (hdegree hrC hbC hzC) (hdegree hrD hbD hzD)
  have htoP : Set.MapsTo (Prod.snd : Q 9 × (Q 9 × Q 9) → Q 9 × Q 9)
      (↑I : Set _) (↑P : Set _) := by
    rintro ⟨z, x, y⟩ hw
    obtain ⟨hprod, hzx, hzy⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (Finset.mem_product.mp hprod).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩,
      distance_two_of_common_neighbor
        (fun hxy => Finset.disjoint_left.mp hdisj hx (hxy ▸ hy)) hzx.symm hzy.symm⟩
  have hupp : I.card ≤ 2 * P.card := by
    have hsum : 2 * P.card = ∑ _p ∈ P, (2 : ℕ) := by simp [Nat.mul_comm]
    rw [hsum, Finset.card_eq_sum_card_fiberwise htoP]
    apply Finset.sum_le_sum
    intro p hp
    have hdist := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro heq
      simp [heq] at hdist
    have hsub : I.filter (fun w => w.2 = p) ⊆
        ((diff p.1 p.2).image (BalancedCriticalSpectrum.flip p.1)).product {p} := by
      rintro ⟨z, x, y⟩ hw
      obtain ⟨hwI, hpair⟩ := Finset.mem_filter.mp hw
      change (x, y) = p at hpair
      subst p
      have hadj : (hypercube 9).Adj z x ∧ (hypercube 9).Adj z y :=
        (Finset.mem_filter.mp hwI).2
      obtain ⟨i, rfl⟩ := adjacent_exists_flip hadj.1.symm
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ (diff_of_adj_flip hne i hadj.2).1, Finset.mem_singleton_self _⟩
    refine (Finset.card_le_card hsub).trans ?_
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, mul_one]
    exact Finset.card_image_le.trans (le_of_eq hdist)
  change 12 ≤ P.card
  omega

#print axioms boundary_card_ge_130_of_no_twenty_half
#print axioms boundary_card_ge_130
#print axioms common_boundary_card_ge_6
#print axioms exists_distance_two_pair
#print axioms distance_two_pairs_card_ge_12

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CommonBoundaryObstruction
