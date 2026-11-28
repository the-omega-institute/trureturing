import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisExcessCycles
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedCutEnergy
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport

/-! With at most three holes in a parity half-fibre, few vertices on the
opposite parity can have subcubic degree in the free directions. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PureFibreEdgeCapacity

open Finset
open scoped symmDiff
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip directionEndpoints directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions mem_directions flip_injective regular_directions)
open Q9IsotropicHuang (parity)
open Q9InactiveContactFibre (freeEdges restrictToFibre sameFibre)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9WeightedCutEnergy (directedPairCount cut_direction_energy)
open HuangThreeColumnIntegrality (neighbors mem_neighbors common_neighbors_card_le_two
  triple_common_neighbor)
open CoordinateHalves.BinaryCubeKernelSupport (cubeFinsetEquiv cubeFinsetEquiv_flip)
open private freeEdges_le_degree_sum flip_same_fibre closedPattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private regular_parity_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram
open private paritySide from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private directedPairCount_symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedCutEnergy

private theorem three_small_union {α : Type*} [DecidableEq α] (A B C : Finset α)
    (ha : A.card ≤ 2) (hb : B.card ≤ 2) (hc : C.card ≤ 2)
    (hcommon : A.Nonempty → B.Nonempty → C.Nonempty → ∃ v ∈ A, v ∈ B ∧ v ∈ C) :
    (A ∪ B ∪ C).card ≤ 4 := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · by_cases hC : C.Nonempty
      · obtain ⟨v, hva, hvb, hvc⟩ := hcommon hA hB hC
        have hsub : (A ∪ B ∪ C).erase v ⊆ A.erase v ∪ B.erase v ∪ C.erase v := by
          intro u hu
          simp only [mem_erase, mem_union] at hu ⊢
          tauto
        have hcard := card_le_card hsub
        have hsum := card_union_le (A.erase v ∪ B.erase v) (C.erase v)
        have hab := card_union_le (A.erase v) (B.erase v)
        have ha' := card_erase_add_one hva
        have hb' := card_erase_add_one hvb
        have hc' := card_erase_add_one hvc
        have htotal := card_erase_add_one
          (mem_union_right (A ∪ B) hvc : v ∈ A ∪ B ∪ C)
        omega
      · rw [not_nonempty_iff_eq_empty.mp hC, union_empty]
        exact (card_union_le A B).trans (by omega)
    · rw [not_nonempty_iff_eq_empty.mp hB, union_empty]
      exact (card_union_le A C).trans (by omega)
  · rw [not_nonempty_iff_eq_empty.mp hA, empty_union]
    exact (card_union_le B C).trans (by omega)

open Classical in
/-- At most three holes allow at most twice one less than their number of
centres adjacent to two distinct holes. -/
theorem small_hole_centers {n : ℕ} (H T : Finset (Finset (Fin n))) (hH : H.card ≤ 3)
    (hT : ∀ z ∈ T, ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ z ∈ neighbors a ∩ neighbors b) :
    T.card ≤ 2 * (H.card - 1) := by
  have hp : T.Nonempty → 2 ≤ H.card := by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha, b, hb, hab, _⟩ := hT z hz
    exact one_lt_card_iff.mpr ⟨a, b, ha, hb, hab⟩
  by_cases hn : 2 ≤ H.card
  · by_cases htwo : H.card = 2
    · obtain ⟨a, b, hab, hEq⟩ := card_eq_two.mp htwo
      have hsub : T ⊆ neighbors a ∩ neighbors b := by
        intro z hz
        obtain ⟨x, hx, y, hy, hxy, hnz⟩ := hT z hz
        simp only [hEq, mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hxy rfl).elim
        · exact hnz
        · simpa only [inter_comm] using hnz
        · exact (hxy rfl).elim
      have hb := (card_le_card hsub).trans (common_neighbors_card_le_two hab)
      omega
    · have hthree : H.card = 3 := by omega
      obtain ⟨a, b, c, hab, hac, hbc, hEq⟩ := card_eq_three.mp hthree
      let A := neighbors a ∩ neighbors b
      let B := neighbors a ∩ neighbors c
      let C := neighbors b ∩ neighbors c
      have hsub : T ⊆ A ∪ B ∪ C := by
        intro z hz
        obtain ⟨x, hx, y, hy, hxy, hnz⟩ := hT z hz
        simp only [hEq, mem_insert, mem_singleton] at hx hy
        simp only [A, B, C, mem_union, mem_inter] at hnz ⊢
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
      have hcommon (ha : A.Nonempty) (hb : B.Nonempty) (hc : C.Nonempty) :
          ∃ v ∈ A, v ∈ B ∧ v ∈ C := by
        obtain ⟨v, hva, hvb, hvc⟩ := triple_common_neighbor hab hac hbc ha hb hc
        exact ⟨v, mem_inter.mpr ⟨hva, hvb⟩, mem_inter.mpr ⟨hva, hvc⟩,
          mem_inter.mpr ⟨hvb, hvc⟩⟩
      have hb := (card_le_card hsub).trans (three_small_union A B C
        (common_neighbors_card_le_two hab) (common_neighbors_card_le_two hac)
        (common_neighbors_card_le_two hbc) hcommon)
      omega
  · have he : T = ∅ := not_nonempty_iff_eq_empty.mp (fun h => hn (hp h))
    simp [he]

open Classical in
private theorem few_holes_bound_with_missing_centres
    (S : Finset (Q 9)) (A : Finset (Fin 9)) (hA : A.card = 5)
    (z : Q 9) (b : Bool) (hdeg : ∀ x ∈ S, (directions S x).card ≤ 3)
    (B : Finset (Q 9)) (hdis : Disjoint S B)
    (hB : ∀ y ∈ B, sameFibre A z y ∧ parity y = !b ∧
      2 ≤ (A.filter (fun i => flip y i ∉ S)).card) :
    let L := (restrictToFibre S A z).filter (fun x => parity x = b)
    let H := (restrictToFibre univ A z).filter (fun x => parity x = b ∧ x ∉ S)
    H.card ≤ 3 → (freeEdges S L A).card + 3 * B.card ≤ 6 * (H.card - 1) := by
  intro L H hsmall
  let P := S.filter (fun y => sameFibre A z y ∧ parity y = !b)
  let g := cubeFinsetEquiv 9
  have hcenters : ((P ∪ B).map g.toEmbedding).card ≤
      2 * ((H.map g.toEmbedding).card - 1) := by
    apply small_hole_centers _ _ (by simpa using hsmall)
    intro u hu
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hu
    let K := A.filter (fun i => flip y i ∉ S)
    obtain ⟨hyF, hyB, hc⟩ : sameFibre A z y ∧ parity y = !b ∧ 2 ≤ K.card := by
      rcases mem_union.mp hy with hyP | hyB
      · obtain ⟨hyS, hyF, hyB⟩ := mem_filter.mp hyP
        refine ⟨hyF, hyB, ?_⟩
        have hsplit := card_filter_add_card_filter_not (s := A) (fun i => flip y i ∈ S)
        rw [hA] at hsplit
        have hsub : (A.filter (fun i => flip y i ∈ S)) ⊆ directions S y :=
          fun i hi => (mem_directions S y i).mpr (mem_filter.mp hi).2
        have hbound := (card_le_card hsub).trans (hdeg y hyS)
        change _ + K.card = 5 at hsplit
        omega
      · exact hB y hyB
    obtain ⟨i, j, hi, hj, hij⟩ := one_lt_card_iff.mp hc
    have hhole (k : Fin 9) (hk : k ∈ K) : flip y k ∈ H := by
      obtain ⟨hkA, hkS⟩ := mem_filter.mp hk
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
      · intro l hl
        exact (flip_same_fibre hkA l hl).trans (hyF l hl)
      · exact ⟨by rw [parity_flip, hyB, Bool.not_not], hkS⟩
    have hne (k : Fin 9) : g y ∈ neighbors (g (flip y k)) := by
      apply mem_image.mpr
      refine ⟨k, mem_univ _, ?_⟩
      change cubeFinsetEquiv 9 (flip y k) ∆ {k} = cubeFinsetEquiv 9 y
      rw [← cubeFinsetEquiv_flip, BalancedCriticalSpectrum.flip_flip]
    exact ⟨g (flip y i), mem_map.mpr ⟨_, hhole i hi, rfl⟩,
      g (flip y j), mem_map.mpr ⟨_, hhole j hj, rfl⟩,
      fun he => hij (flip_injective y (g.injective he)), mem_inter.mpr ⟨hne i, hne j⟩⟩
  have hPB : Disjoint P B :=
    disjoint_of_subset_left (filter_subset _ _) hdis
  have hP : P.card + B.card ≤ 2 * (H.card - 1) := by
    simpa only [card_map, card_union_of_disjoint hPB] using hcenters
  let rev (p : Q 9 × Fin 9) : Q 9 × Fin 9 := (flip p.1 p.2, p.2)
  have hinj : Function.Injective rev := by
    apply Function.Involutive.injective
    intro ⟨x, i⟩
    simp [rev]
  have hsubset : (freeEdges S L A).image rev ⊆ freeEdges S P A := by
    intro q hq
    obtain ⟨⟨x, i⟩, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨hxa, hiS⟩ := mem_filter.mp hp
    obtain ⟨hx, hiA⟩ := mem_product.mp hxa
    obtain ⟨hxf, hxb⟩ := mem_filter.mp hx
    obtain ⟨hxS, hxF⟩ := mem_filter.mp hxf
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hiS, ?_⟩, hiA⟩, ?_⟩
    · refine ⟨?_, by rw [parity_flip, hxb]⟩
      intro j hj
      exact (flip_same_fibre hiA j hj).trans (hxF j hj)
    · simpa [rev] using hxS
  have he := (card_le_card hsubset).trans
    (freeEdges_le_degree_sum (fun x hx => hdeg x (mem_filter.mp hx).1))
  rw [card_image_of_injective _ hinj] at he
  omega

open Classical in
/-- Free edges in a subcubic component with at most three holes on a
five-axis parity fibre satisfy an upper bound determined by those holes. -/
theorem few_holes_bound_freeEdges (S : Finset (Q 9)) (A : Finset (Fin 9)) (hA : A.card = 5)
    (z : Q 9) (b : Bool) (hdeg : ∀ x ∈ S, (directions S x).card ≤ 3) :
    let L := (restrictToFibre S A z).filter (fun x => parity x = b)
    let H := (restrictToFibre univ A z).filter (fun x => parity x = b ∧ x ∉ S)
    H.card ≤ 3 → (freeEdges S L A).card ≤ 6 * (H.card - 1) := by
  simpa using few_holes_bound_with_missing_centres S A hA z b hdeg ∅ (by simp) (by simp)

open Classical in
/-- A missing opposite-parity vertex with two missing neighbours consumes one
of the available centres and lowers the small-hole edge bound by three. -/
theorem few_holes_bound_freeEdges_of_missing_centre
    (S : Finset (Q 9)) (A : Finset (Fin 9)) (hA : A.card = 5)
    (z : Q 9) (b : Bool) (hdeg : ∀ x ∈ S, (directions S x).card ≤ 3)
    {y : Q 9} (hy : y ∉ S) (hyf : sameFibre A z y) (hyp : parity y = !b)
    {j k : Fin 9} (hj : j ∈ A) (hk : k ∈ A) (hjk : j ≠ k)
    (hjS : flip y j ∉ S) (hkS : flip y k ∉ S) :
    let L := (restrictToFibre S A z).filter (fun x => parity x = b)
    let H := (restrictToFibre univ A z).filter (fun x => parity x = b ∧ x ∉ S)
    H.card ≤ 3 → (freeEdges S L A).card + 6 ≤ 5 * H.card := by
  intro L H hsmall
  have hp : 2 ≤ (A.filter (fun i => flip y i ∉ S)).card :=
    one_lt_card_iff.mpr ⟨j, k, mem_filter.mpr ⟨hj, hjS⟩, mem_filter.mpr ⟨hk, hkS⟩, hjk⟩
  have h := few_holes_bound_with_missing_centres S A hA z b hdeg {y}
    (by simpa using hy) (by simpa using And.intro hyf (And.intro hyp hp)) hsmall
  change (freeEdges S L A).card + 3 * ({y} : Finset (Q 9)).card ≤ 6 * (H.card - 1) at h
  simp only [card_singleton, mul_one] at h
  have hH {i : Fin 9} (hi : i ∈ A) (hiS : flip y i ∉ S) : flip y i ∈ H := by
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · intro l hl
      exact (flip_same_fibre hi l hl).trans (hyf l hl)
    · exact ⟨by rw [parity_flip, hyp, Bool.not_not], hiS⟩
  have htwo : 2 ≤ H.card := one_lt_card_iff.mpr
    ⟨_, _, hH hj hjS, hH hk hkS, fun he => hjk (flip_injective y he)⟩
  omega

open Classical in
/-- With at most three holes, a pure side facing the opposite component
across two forbidden parity corrections contributes at most three edges
for two holes and nine edges for three holes. -/
theorem adjacent_fibre_small_hole_edge_capacity {C D : Finset (Q 9)} (b : Bool) {x : Q 9}
    (hx : x ∈ C) (hp : parity x = b)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (A : Finset (Fin 9)) (hA : A.card = 5) {i j k : Fin 9}
    (hi : i ∉ A) (hj : j ∈ A) (hk : k ∈ A) (hjk : j ≠ k)
    (hmj : ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hmk : ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hdeg : ∀ v ∈ D, (directions D v).card ≤ 3) :
    let y := flip x i
    let L := (restrictToFibre D A y).filter (fun v => parity v = b)
    let H := (restrictToFibre univ A y).filter (fun v => parity v = b ∧ v ∉ D)
    H.card ≤ 3 → (freeEdges D L A).card + 6 ≤ 5 * H.card := by
  have hne (l : Fin 9) (hl : l ∈ A) : i ≠ l := fun he => hi (he.symm ▸ hl)
  obtain ⟨hy, hpar, hjD, hkD⟩ :=
    Q9InactiveContactFibre.adjacent_fibre_missing_centre b hx hp hsep
      (hne j hj) (hne k hk) hmj hmk
  exact few_holes_bound_freeEdges_of_missing_centre D A hA (flip x i) b hdeg
    hy (fun _ _ => rfl) hpar hj hk hjk hjD hkD

open scoped BigOperators in
/-- Eleven holes spread among pure fibres, with at least four of those fibres
having two or more holes, allow at most sixty edges in the free directions. -/
theorem pure_edge_budget {α : Type*} (P : Finset α) (holes edges : α → ℕ)
    (hbudget : (∑ p ∈ P, holes p) ≤ 11)
    (hboundary : 4 ≤ (P.filter (fun p => 2 ≤ holes p)).card)
    (hsmall : ∀ p ∈ P, holes p ≤ 3 → edges p ≤ 6 * (holes p - 1))
    (hdeg : ∀ p ∈ P, edges p ≤ 3 * (16 - holes p)) :
    (∑ p ∈ P, edges p) ≤ 60 := by
  let flag (k : ℕ) (p : α) : ℕ := if k ≤ holes p then 1 else 0
  let B := P.filter (fun p => 2 ≤ holes p)
  let H := P.filter (fun p => 4 ≤ holes p)
  have hcounts : 2 * B.card + 2 * H.card ≤ ∑ p ∈ P, holes p := by
    calc
      _ = ∑ p ∈ P, (2 * flag 2 p + 2 * flag 4 p) := by
        simp only [sum_add_distrib, ← mul_sum, flag, sum_boole, Nat.cast_id, B, H]
      _ ≤ _ := by
        apply sum_le_sum
        intro p _
        by_cases h₄ : 4 ≤ holes p <;> by_cases h₂ : 2 ≤ holes p <;>
          simp [flag, h₄, h₂] <;> omega
  have he : (∑ p ∈ P, edges p) + 6 * B.card ≤ 6 * (∑ p ∈ P, holes p) + 18 * H.card := by
    calc
      _ = ∑ p ∈ P, (edges p + 6 * flag 2 p) := by
        simp only [sum_add_distrib, ← mul_sum, flag, sum_boole, Nat.cast_id, B]
      _ ≤ ∑ p ∈ P, (6 * holes p + 18 * flag 4 p) := by
        apply sum_le_sum
        intro p hp
        by_cases h₄ : 4 ≤ holes p
        · have h₂ : 2 ≤ holes p := by omega
          have hd := hdeg p hp
          simp only [flag, if_pos h₄, if_pos h₂]
          omega
        · have hs := hsmall p hp (by omega)
          by_cases h₂ : 2 ≤ holes p <;> simp [flag, h₄, h₂] <;> omega
      _ = _ := by simp only [sum_add_distrib, ← mul_sum, flag, sum_boole, Nat.cast_id, H]
  change 4 ≤ B.card at hboundary
  omega

private theorem two_closed_patterns_card :
    ∀ p q, p ≠ q → 8 ≤ (closedPattern p ∪ closedPattern q).card := by decide

open scoped BigOperators in
/-- The fibre capacities force all eleven other patterns to be mixed when
the four-cube has exactly five occupied pure fibres. -/
theorem five_pure_forces_eleven_mixed (P M : Finset (Q 4)) (holes edges : Q 4 → ℕ)
    (hpure : P.card = 5) (hmixed : M.card ≤ 11) (hdis : Disjoint P M)
    (hnear : ∀ p ∈ P, ∀ i : Fin 4, flip p i ∈ M → 2 ≤ holes p)
    (hsize : 129 + (∑ p ∈ P, holes p) ≤ 6 * M.card + 80)
    (hedges : 215 ≤ 15 * M.card + (∑ p ∈ P, edges p))
    (hsmall : ∀ p ∈ P, holes p ≤ 3 → edges p ≤ 6 * (holes p - 1))
    (hdeg : ∀ p ∈ P, edges p ≤ 3 * (16 - holes p)) :
    M.card = 11 := by
  by_contra hne
  have hmin : 9 ≤ M.card := by omega
  have hcomp : (univ \ M).card + M.card = 16 := by
    rw [card_sdiff_add_card_eq_card (subset_univ M)]
    decide
  let D := P.filter (fun p => holes p < 2)
  have hball (p : Q 4) (hp : p ∈ D) : closedPattern p ⊆ univ \ M := by
    obtain ⟨hpP, hpH⟩ := mem_filter.mp hp
    intro q hq
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hqM
    rcases mem_insert.mp hq with rfl | hq
    · exact disjoint_left.mp hdis hpP hqM
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hq
      exact (Nat.not_lt_of_ge (hnear p hpP i hqM)) hpH
  have hdense : D.card ≤ 1 := by
    by_contra! h
    obtain ⟨p, q, hp, hq, hpq⟩ := one_lt_card_iff.mp h
    have hu := (two_closed_patterns_card p q hpq).trans
      (card_le_card (union_subset (hball p hp) (hball q hq)))
    omega
  have hpartition : (P.filter (fun p => 2 ≤ holes p)).card + D.card = P.card := by
    simpa only [D, not_le] using
      (card_filter_add_card_filter_not (s := P) (fun p => 2 ≤ holes p))
  have hbound := pure_edge_budget P holes edges (by omega) (by omega) hsmall hdeg
  omega

open scoped BigOperators in
private theorem freeEdges_eq_sum_directionEdges (S : Finset (Q 9)) (A : Finset (Fin 9))
    (b : Bool) :
    (freeEdges S (S.filter (fun x => parity x = b)) A).card = ∑ i ∈ A, directionEdges S i := by
  classical
  let E := freeEdges S (S.filter (fun x => parity x = b)) A
  have hmap (p : Q 9 × Fin 9) (hp : p ∈ E) : p.2 ∈ A :=
    (mem_product.mp (mem_filter.mp hp).1).2
  change E.card = _
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := A) hmap]
  apply sum_congr rfl
  intro i hi
  let P := (directionEndpoints S i).filter (fun x => parity x = b)
  let R := (directionEndpoints S i).filter (fun x => parity x ≠ b)
  have hPR : P.card = R.card := by
    apply card_bij' (fun x _ => flip x i) (fun x _ => flip x i)
    · intro x hx
      obtain ⟨hs, hb⟩ := mem_filter.mp hx
      obtain ⟨hxS, hiS⟩ := mem_filter.mp hs
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hiS, by simpa using hxS⟩, ?_⟩
      rw [parity_flip, hb]
      cases b <;> decide
    · intro x hx
      obtain ⟨hs, hb⟩ := mem_filter.mp hx
      obtain ⟨hxS, hiS⟩ := mem_filter.mp hs
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hiS, by simpa using hxS⟩, ?_⟩
      exact (parity_flip x i).trans (Bool.not_eq_iff.mpr hb)
    · intro x _
      exact BalancedCriticalSpectrum.flip_flip x i
    · intro x _
      exact BalancedCriticalSpectrum.flip_flip x i
  have hsum : P.card + R.card = 2 * directionEdges S i :=
    (card_filter_add_card_filter_not (fun x => parity x = b)).trans (endpoint_card_twice S i)
  have hcard : P.card = directionEdges S i := by omega
  let tag (x : Q 9) : Q 9 × Fin 9 := (x, i)
  have htag : P.image tag = E.filter (fun v => v.2 = i) := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
      obtain ⟨hs, hb⟩ := mem_filter.mp hx
      obtain ⟨hxS, hiS⟩ := mem_filter.mp hs
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hxS, hb⟩, hi⟩, hiS⟩, rfl⟩
    · rintro hv
      obtain ⟨he, hq⟩ := mem_filter.mp hv
      obtain ⟨hp, hx⟩ := mem_filter.mp he
      obtain ⟨hl, _⟩ := mem_product.mp hp
      obtain ⟨hs, hb⟩ := mem_filter.mp hl
      refine mem_image.mpr ⟨v.1, mem_filter.mpr ⟨mem_filter.mpr ⟨hs, ?_⟩, hb⟩, ?_⟩
      · exact hq ▸ hx
      · exact Prod.ext rfl hq.symm
  rw [← htag, card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), hcard]

open scoped BigOperators in
/-- Opposite parity shores of a balanced cube support have a crossing-count
bound on any chosen family of directions. -/
theorem parity_cut_edge_square_le (L R : Finset (Q 9)) (b : Bool) (A : Finset (Fin 9))
    (hl : ∀ x ∈ L, parity x = b) (hr : ∀ x ∈ R, parity x = !b)
    (hbal : BalancedCriticalSpectrum.IsBalanced (L ∪ R)) :
    (∑ i ∈ A, (directedPairCount L R i : ℝ)) ^ 2 ≤
      (A.card : ℝ) * ((L.card : ℝ) * R.card) := by
  classical
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · have hd : Disjoint L R := disjoint_left.mpr (by
        intro x hxl hxr
        have h := (hl x hxl).symm.trans (hr x hxr)
        cases b <;> simp at h)
      have hzero (S : Finset (Q 9)) (c : Bool)
          (hS : ∀ x ∈ S, parity x = c) (i : Fin 9) : directedPairCount S S i = 0 := by
        apply card_eq_zero.mpr
        apply not_nonempty_iff_eq_empty.mp
        rintro ⟨x, hx⟩
        obtain ⟨hs, hf⟩ := mem_filter.mp hx
        have h := hS _ hf
        rw [parity_flip, hS _ hs] at h
        cases c <;> simp at h
      let n : ℝ := L.card
      let q : ℝ := R.card
      have hn : 0 < n := by
        change (0 : ℝ) < (L.card : ℝ)
        exact_mod_cast card_pos.mpr hL
      have hq : 0 < q := by
        change (0 : ℝ) < (R.card : ℝ)
        exact_mod_cast card_pos.mpr hR
      let s := Real.sqrt q
      let t := Real.sqrt n
      have hs : s ^ 2 = q := Real.sq_sqrt hq.le
      have ht : t ^ 2 = n := Real.sq_sqrt hn.le
      have he := cut_direction_energy L R hd hbal s t
      simp only [hzero L b hl, hzero R (!b) hr, Nat.cast_zero, zero_mul, zero_add, hs, ht] at he
      have hrewrite (i : Fin 9) :
          (2 * (directedPairCount L R i : ℝ) * s * t) ^ 2 =
            (4 * (n * q)) * (directedPairCount L R i : ℝ) ^ 2 := by
        calc
          _ = 4 * (t ^ 2 * s ^ 2) * (directedPairCount L R i : ℝ) ^ 2 := by ring
          _ = _ := by rw [hs, ht]
      rw [sum_congr rfl (fun i _ => hrewrite i), ← mul_sum] at he
      have hsum : (∑ i : Fin 9, (directedPairCount L R i : ℝ) ^ 2) ≤ n * q := by
        apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 4 * (n * q) by positivity)
        calc
          _ ≤ (n * q + q * n) ^ 2 := he
          _ = _ := by ring
      have hsub := sum_le_sum_of_subset_of_nonneg (subset_univ A)
        (fun i _ _ => sq_nonneg (directedPairCount L R i : ℝ))
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ))
        (fun i => (directedPairCount L R i : ℝ))
      simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
      exact hcs.trans (mul_le_mul_of_nonneg_left (hsub.trans hsum) (by positivity))
    · simp [not_nonempty_iff_eq_empty.mp hR, directedPairCount]
  · simp [not_nonempty_iff_eq_empty.mp hL, directedPairCount]

open Classical in
open scoped BigOperators in
/-- In a five-axis fibre, the squared number of selected free edges is
bounded by the selected parity size and its number of holes. -/
theorem five_axis_hole_energy (S : Finset (Q 9)) (A : Finset (Fin 9)) (hA : A.card = 5)
    (z : Q 9) (b : Bool) (hbal : BalancedCriticalSpectrum.IsBalanced S) :
    let L := (restrictToFibre S A z).filter (fun x => parity x = b)
    let H := (restrictToFibre univ A z).filter (fun x => parity x = b ∧ x ∉ S)
    let E := (freeEdges S L A).card
    E ^ 2 ≤ 5 * (L.card * (H.card + E / 5)) := by
  intro L H E
  let R := (restrictToFibre S A z).filter (fun x => parity x = !b)
  have hm {T : Finset (Q 9)} {x : Q 9} {p : Bool}
      (h : x ∈ (restrictToFibre T A z).filter (fun v => parity v = p)) :
      x ∈ T ∧ sameFibre A z x ∧ parity x = p :=
    ⟨(mem_filter.mp (mem_filter.mp h).1).1, (mem_filter.mp (mem_filter.mp h).1).2,
      (mem_filter.mp h).2⟩
  have hflip {x : Q 9} {i : Fin 9} (hx : sameFibre A z x) (hi : i ∈ A) :
      sameFibre A z (flip x i) :=
    fun j hj => (flip_same_fibre hi j hj).trans (hx j hj)
  have hE : E = ∑ i ∈ A, directedPairCount L R i := by
    let edges := freeEdges S L A
    change edges.card = _
    have hmap (p : Q 9 × Fin 9) (hp : p ∈ edges) : p.2 ∈ A :=
      (mem_product.mp (mem_filter.mp hp).1).2
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := A) hmap]
    apply sum_congr rfl
    intro i hi
    unfold directedPairCount
    apply card_bij (fun p _ => p.1)
    · intro p hp
      obtain ⟨he, hpi⟩ := mem_filter.mp hp
      obtain ⟨ha, hs⟩ := mem_filter.mp he
      have hx := (mem_product.mp ha).1
      obtain ⟨_, hxf, hxb⟩ := hm hx
      have hf : flip p.1 i ∈ S := hpi ▸ hs
      exact mem_filter.mpr ⟨hx, mem_filter.mpr
        ⟨mem_filter.mpr ⟨hf, hflip hxf hi⟩, (parity_flip p.1 i).trans (congrArg Bool.not hxb)⟩⟩
    · intro p hp q hq he
      exact Prod.ext he ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
    · intro x hx
      obtain ⟨hxL, hxR⟩ := mem_filter.mp hx
      exact ⟨(x, i), mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hxL, hi⟩, (hm hxR).1⟩, rfl⟩, rfl⟩
  have hsplit (i : Fin 9) (hi : i ∈ A) :
      directedPairCount R L i + directedPairCount R H i = R.card := by
    have he : R.filter (fun x => flip x i ∉ L) = R.filter (fun x => flip x i ∈ H) := by
      ext x
      simp only [mem_filter]
      apply and_congr_right
      intro hx
      obtain ⟨_, hxf, hxb⟩ := hm hx
      have hf := hflip hxf hi
      have hb : parity (flip x i) = b := by rw [parity_flip, hxb, Bool.not_not]
      have hs : flip x i ∈ L ↔ flip x i ∈ S := by
        constructor
        · exact fun h => (hm h).1
        · exact fun h => mem_filter.mpr ⟨mem_filter.mpr ⟨h, hf⟩, hb⟩
      rw [hs]
      change _ ↔ BalancedCriticalSpectrum.flip x i ∈ (restrictToFibre univ A z).filter _
      simp [restrictToFibre, hf, hb]
    unfold directedPairCount
    rw [← he]
    exact card_filter_add_card_filter_not _
  have hsum : E + (∑ i ∈ A, directedPairCount R H i) = 5 * R.card := by
    rw [hE, ← sum_add_distrib]
    calc
      _ = ∑ _ ∈ A, R.card := sum_congr rfl fun i hi => by
        rw [directedPairCount_symm L R]
        exact hsplit i hi
      _ = _ := by simp [hA]
  have hholes : (∑ i ∈ A, directedPairCount R H i) ≤ 5 * H.card := by
    calc
      _ ≤ ∑ _ ∈ A, H.card := sum_le_sum fun i _ => by
        rw [directedPairCount_symm R H]
        exact card_le_card (filter_subset _ _)
      _ = _ := by simp [hA]
  have hq : R.card ≤ H.card + E / 5 := by omega
  have hb : BalancedCriticalSpectrum.IsBalanced (L ∪ R) := by
    obtain ⟨σ, hσ⟩ := hbal
    have hsub (x : Q 9) (hx : x ∈ L ∪ R) : x ∈ S :=
      (mem_union.mp hx).elim (fun h => (hm h).1) (fun h => (hm h).1)
    exact ⟨σ, ⟨fun x hx => hσ.1 x (hsub x hx),
      fun x hx y hy he => hσ.2 x (hsub x hx) y (hsub y hy) he⟩⟩
  have he := parity_cut_edge_square_le L R b A (fun x hx => (hm hx).2.2)
    (fun x hx => (hm hx).2.2) hb
  rw [hA] at he
  have hnat : E ^ 2 ≤ 5 * (L.card * R.card) := by
    rw [hE]
    exact_mod_cast he
  exact hnat.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq))

private theorem middle_hole_energy_bound :
    ∀ (h : Fin 7) (v : Fin 49), 4 ≤ h.val →
      v.val ^ 2 ≤ 5 * ((16 - h.val) * (h.val + v.val / 5)) →
      v.val ≤ 5 * h.val + 1 ∧ (h.val = 6 → v.val ≤ 22) := by decide

open Classical in
/-- The signed hole bound and subcubic degree bound give a linear free-edge
bound, with a sharper value at six holes. -/
theorem five_axis_hole_linear_bound (S : Finset (Q 9)) (e : Fin 5 ↪ Fin 9)
    {i : Fin 9} (hi : i ∉ univ.map e) (z : Q 9) (b : Bool)
    (hbal : BalancedCriticalSpectrum.IsBalanced S)
    (hdeg : ∀ x ∈ S, (directions S x).card ≤ 3) :
    let A := univ.map e
    let L := (restrictToFibre S A z).filter (fun x => parity x = b)
    let H := (restrictToFibre univ A z).filter (fun x => parity x = b ∧ x ∉ S)
    let E := (freeEdges S L A).card
    E ≤ 5 * H.card + 1 ∧ (H.card = 6 → E ≤ 22) := by
  intro A L H E
  let F := (restrictToFibre univ A z).filter (fun x => parity x = b)
  have hF : F.card ≤ 16 := by
    have h := Q9InactiveContactFibre.adjacent_fibre_capacity (C := ∅) (D := univ) b
      (flip z i) e hi ∅ (empty_subset _) (by simp)
    simpa [F, A] using h
  have hselected : F.filter (fun x => x ∈ S) = L := by
    ext x
    simp only [F, L, restrictToFibre, mem_filter, mem_univ, true_and]
    tauto
  have hholes : F.filter (fun x => x ∉ S) = H := by
    ext x
    simp [F, H, restrictToFibre, and_assoc]
  have hc := card_filter_add_card_filter_not (s := F) (fun x => x ∈ S)
  rw [hselected, hholes] at hc
  have hdegree : E ≤ 3 * L.card :=
    freeEdges_le_degree_sum (fun x hx => hdeg x (mem_filter.mp (mem_filter.mp hx).1).1)
  have hA : A.card = 5 := by simp [A]
  by_cases hsmall : H.card ≤ 3
  · have hs := few_holes_bound_freeEdges S A hA z b hdeg hsmall
    change E ≤ 6 * (H.card - 1) at hs
    omega
  by_cases hlarge : 7 ≤ H.card
  · omega
  have hL : L.card ≤ 16 - H.card := by omega
  have hspec := five_axis_hole_energy S A hA z b hbal
  change E ^ 2 ≤ 5 * (L.card * (H.card + E / 5)) at hspec
  have hspec' := hspec.trans
    (Nat.mul_le_mul_left 5 (Nat.mul_le_mul_right (H.card + E / 5) hL))
  have hh : 4 ≤ H.card := by omega
  exact middle_hole_energy_bound ⟨H.card, by omega⟩ ⟨E, by omega⟩ hh hspec'

open Classical in
/-- An occupied neighbouring fibre of the other component and two forbidden
parity corrections lower the free-edge budget by six below five times the
number of holes. -/
theorem adjacent_fibre_hole_edge_capacity {C D : Finset (Q 9)} (b : Bool) {x : Q 9}
    (hx : x ∈ C) (hp : parity x = b)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (e : Fin 5 ↪ Fin 9) {i j k : Fin 9}
    (hi : i ∉ univ.map e) (hj : j ∈ univ.map e) (hk : k ∈ univ.map e) (hjk : j ≠ k)
    (hmj : ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hmk : ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hbal : BalancedCriticalSpectrum.IsBalanced D)
    (hdeg : ∀ v ∈ D, (directions D v).card ≤ 3) :
    let y := flip x i
    let A := univ.map e
    let L := (restrictToFibre D A y).filter (fun v => parity v = b)
    let H := (restrictToFibre univ A y).filter (fun v => parity v = b ∧ v ∉ D)
    (freeEdges D L A).card + 6 ≤ 5 * H.card := by
  intro y A L H
  by_cases hs : H.card ≤ 3
  · exact adjacent_fibre_small_hole_edge_capacity b hx hp hsep A (by simp [A])
      hi hj hk hjk hmj hmk hdeg hs
  by_cases hm : H.card = 4 ∨ H.card = 5
  · exact Q9FiveAxisExcessCycles.adjacent_fibre_four_five_hole_capacity
      b hx hp hsep e hi hj hk hjk hmj hmk hbal hdeg hm
  by_cases h6 : H.card = 6
  · have hb := (five_axis_hole_linear_bound D e hi y b hbal hdeg).2 h6
    change (freeEdges D L A).card ≤ 22 at hb
    omega
  let F := (restrictToFibre univ A y).filter (fun v => parity v = b)
  have hF : F.card ≤ 16 := by
    have hb := Q9InactiveContactFibre.adjacent_fibre_capacity (C := ∅) (D := univ) b
      x e hi ∅ (empty_subset _) (by simp)
    simpa [F, A, y] using hb
  have hL : F.filter (fun v => v ∈ D) = L := by
    ext v
    simp [F, L, restrictToFibre, and_comm, and_assoc]
  have hH : F.filter (fun v => v ∉ D) = H := by
    ext v
    simp [F, H, restrictToFibre, and_assoc]
  have hsplit := card_filter_add_card_filter_not (s := F) (fun v => v ∈ D)
  rw [hL, hH] at hsplit
  have he : (freeEdges D L A).card ≤ 3 * L.card :=
    freeEdges_le_degree_sum (fun v hv => hdeg v (mem_filter.mp (mem_filter.mp hv).1).1)
  omega

open private five_axis_cross_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre

open Classical in
/-- A bank in a mixed fibre lies among the free neighbours of the antipode
of an opposite-bank point. Its two forbidden translations intersect in at
most two points, so they exclude at least twice its size minus two. -/
theorem adjacent_fibre_majority_hole_capacity {C D : Finset (Q 9)} (b : Bool) (z : Q 9)
    (e : Fin 5 ↪ Fin 9) {i j k : Fin 9} (hi : i ∉ univ.map e)
    (hj : j ∈ univ.map e) (hk : k ∈ univ.map e) (hjk : j ≠ k)
    (hmj : ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hmk : ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hmask : ∀ T ∈ minimumDisplacements C D b 2, ¬ T ⊆ univ.map e) :
    let A := univ.map e
    let L := (restrictToFibre C A z).filter (fun x => parity x = b)
    let R := (restrictToFibre D A (flip z i)).filter (fun x => parity x = b)
    ((restrictToFibre D A z).filter (fun x => parity x = b)).Nonempty →
      2 * L.card + R.card ≤ 18 := by
  intro A L R hD
  obtain ⟨x, hx⟩ := hD
  obtain ⟨hxF, hxb⟩ := mem_filter.mp hx
  obtain ⟨hxD, hxF⟩ := mem_filter.mp hxF
  let t : Q 9 := fun l => if l ∈ A then !x l else x l
  have hnear (y : Q 9) (hy : y ∈ L) : ∃ l ∈ A, y = flip t l := by
    obtain ⟨hyF, hyb⟩ := mem_filter.mp hy
    obtain ⟨hyC, hyF⟩ := mem_filter.mp hyF
    have hA : A.card = 5 := by simp [A]
    have hd := five_axis_cross_distance b z A hA hsep hmask hyC hxD hyb hxb hyF hxF
    rw [hammingDist_comm] at hd
    change (univ.filter (fun l => x l ≠ y l)).card = 4 at hd
    let same := A.filter (fun l => x l = y l)
    have hdiff : A.filter (fun l => x l ≠ y l) = univ.filter (fun l => x l ≠ y l) := by
      ext l
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro hn
      by_contra hl
      exact hn ((hxF l hl).trans (hyF l hl).symm)
    have hcount := card_filter_add_card_filter_not (s := A) (fun l => x l = y l)
    rw [hdiff, hd, hA] at hcount
    obtain ⟨l, hl⟩ := card_eq_one.mp (show same.card = 1 by dsimp [same]; omega)
    obtain ⟨hlA, hlxy⟩ := mem_filter.mp (show l ∈ same by simp [hl])
    refine ⟨l, hlA, ?_⟩
    funext q
    by_cases he : q = l
    · subst q
      simpa [t, hlA] using hlxy.symm
    · by_cases hq : q ∈ A
      · have hdxy : x q ≠ y q := by
          intro h
          exact he (mem_singleton.mp (hl ▸ mem_filter.mpr ⟨hq, h⟩))
        simpa [t, BalancedCriticalSpectrum.flip, he, hq] using
          (Bool.eq_not_of_ne (Ne.symm hdxy))
      · simpa [t, BalancedCriticalSpectrum.flip, he, hq] using
          (hyF q hq).trans (hxF q hq).symm
  let tau (l : Fin 9) (y : Q 9) := flip (flip y i) l
  let move (l : Fin 9) := L.image (tau l)
  have invol (a : Fin 9) : Function.Involutive (fun y : Q 9 => flip y a) :=
    fun _ => BalancedCriticalSpectrum.flip_flip _ _
  have hcard (l : Fin 9) : (move l).card = L.card :=
    card_image_of_injective _ ((invol l).injective.comp (invol i).injective)
  let g := cubeFinsetEquiv 9
  have hmaps {l : Fin 9} {y : Q 9} (hy : y ∈ move l) : g y ∈ neighbors (g (tau l t)) := by
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hy
    obtain ⟨a, _, rfl⟩ := hnear u hu
    have he : tau l (flip t a) = flip (tau l t) a := by
      dsimp [tau]
      rw [BalancedCubeGirth.flip_comm t a i, BalancedCubeGirth.flip_comm (flip t i) a l]
    rw [he]
    exact mem_image.mpr ⟨a, mem_univ _, (cubeFinsetEquiv_flip _ _).symm⟩
  have hjk' : g (tau j t) ≠ g (tau k t) :=
    fun he => hjk (flip_injective (flip t i) (g.injective he))
  have hsub : ((move j ∩ move k).map g.toEmbedding) ⊆
      neighbors (g (tau j t)) ∩ neighbors (g (tau k t)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact mem_inter.mpr ⟨hmaps (mem_inter.mp hy).1, hmaps (mem_inter.mp hy).2⟩
  have hinter := (card_le_card hsub).trans (common_neighbors_card_le_two hjk')
  rw [card_map] at hinter
  have hsum := card_union_add_card_inter (move j) (move k)
  rw [hcard, hcard] at hsum
  have hB : ({j, k} : Finset (Fin 9)) ⊆ A := by
    intro l hl
    simp only [mem_insert, mem_singleton] at hl
    rcases hl with rfl | rfl <;> assumption
  have hm (l : Fin 9) (hl : l ∈ ({j, k} : Finset (Fin 9))) :
      ({i, l} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2 := by
    simp only [mem_insert, mem_singleton] at hl
    rcases hl with rfl | rfl <;> assumption
  have hb := Q9InactiveContactFibre.adjacent_fibre_capacity b z e hi {j, k} hB hm
  change (({j, k} : Finset (Fin 9)).biUnion move).card + R.card ≤ 16 at hb
  rw [biUnion_insert, singleton_biUnion] at hb
  omega

open scoped BigOperators in
private theorem pure_edge_capacity_sum (P M : Finset (Q 4)) (holes edges : Q 4 → ℕ)
    (hline : ∀ p ∈ P, edges p ≤ 5 * holes p + 1)
    (hboundary : ∀ p ∈ P, (∃ i : Fin 4, flip p i ∈ M) → edges p + 6 ≤ 5 * holes p) :
    (∑ p ∈ P, edges p) + 7 * (P.filter (fun p => ∃ i : Fin 4, flip p i ∈ M)).card ≤
      5 * (∑ p ∈ P, holes p) + P.card := by
  classical
  let boundary (p : Q 4) : ℕ := if ∃ i : Fin 4, flip p i ∈ M then 1 else 0
  calc
    _ = ∑ p ∈ P, (edges p + 7 * boundary p) := by
      simp only [sum_add_distrib, ← mul_sum, boundary, sum_boole, Nat.cast_id]
    _ ≤ ∑ p ∈ P, (5 * holes p + 1) := by
      apply sum_le_sum
      intro p hp
      by_cases hm : ∃ i : Fin 4, flip p i ∈ M
      · have h := hboundary p hp hm
        simp only [boundary, if_pos hm]
        omega
      · simpa [boundary, hm] using hline p hp
    _ = _ := by simp [sum_add_distrib, ← mul_sum]

private theorem at_most_one_pure_interior (P M : Finset (Q 4)) (hdis : Disjoint P M)
    (hm : 9 ≤ M.card) :
    (P.filter (fun p => ¬ ∃ i : Fin 4, flip p i ∈ M)).card ≤ 1 := by
  classical
  let I := P.filter (fun p => ¬ ∃ i : Fin 4, flip p i ∈ M)
  change I.card ≤ 1
  by_contra! h
  obtain ⟨p, q, hp, hq, hpq⟩ := one_lt_card_iff.mp h
  have hsub (z : Q 4) (hz : z ∈ I) : closedPattern z ⊆ univ \ M := by
    obtain ⟨hzP, hzM⟩ := mem_filter.mp hz
    intro u hu
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hM
    rcases mem_insert.mp hu with rfl | hu
    · exact disjoint_left.mp hdis hzP hM
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      exact hzM ⟨i, hM⟩
  have hu := (two_closed_patterns_card p q hpq).trans
    (card_le_card (union_subset (hsub p hp) (hsub q hq)))
  have htotal : (univ \ M).card + M.card = 16 := by
    rw [card_sdiff_add_card_eq_card (subset_univ M)]
    decide
  omega

open scoped BigOperators in
/-- At least nine mixed fibres leave at most one pure interior. The free
edge requirement then bounds the total deficits of the mixed fibres. -/
theorem mixed_fibre_deficit_capacity (P M : Finset (Q 4)) (holes edges : Q 4 → ℕ)
    (hm : 9 ≤ M.card) (hdis : Disjoint P M) (deficit loss : ℕ)
    (hoccupancy : 129 + deficit + (∑ p ∈ P, holes p) ≤ 6 * M.card + 16 * P.card)
    (hedges : 215 + loss ≤ 15 * M.card + (∑ p ∈ P, edges p))
    (hline : ∀ p ∈ P, edges p ≤ 5 * holes p + 1)
    (hboundary : ∀ p ∈ P, (∃ i : Fin 4, flip p i ∈ M) → edges p + 6 ≤ 5 * holes p) :
    853 + 5 * deficit + loss ≤ 74 * P.card + 45 * M.card := by
  classical
  have hcap := pure_edge_capacity_sum P M holes edges hline hboundary
  have hi := at_most_one_pure_interior P M hdis hm
  have hsplit := card_filter_add_card_filter_not (s := P) (fun p => ∃ i : Fin 4, flip p i ∈ M)
  omega

open scoped BigOperators in
/-- With six pure fibres, the linear free-edge bounds force ten mixed
fibres and constrain the sum of their occupancy and edge deficits. -/
theorem six_pure_fibre_capacity (P M : Finset (Q 4)) (holes edges : Q 4 → ℕ)
    (hp : P.card = 6) (hdis : Disjoint P M) (deficit loss : ℕ)
    (hoccupancy : 129 + deficit + (∑ p ∈ P, holes p) ≤ 6 * M.card + 96)
    (hedges : 215 + loss ≤ 15 * M.card + (∑ p ∈ P, edges p))
    (hline : ∀ p ∈ P, edges p ≤ 5 * holes p + 1)
    (hboundary : ∀ p ∈ P, (∃ i : Fin 4, flip p i ∈ M) → edges p + 6 ≤ 5 * holes p) :
    M.card = 10 ∧ 5 * deficit + loss ≤ 41 := by
  classical
  have hsum : P.card + M.card ≤ 16 := by
    rw [← card_union_of_disjoint hdis]
    exact (card_le_univ _).trans (by decide)
  have hcap := pure_edge_capacity_sum P M holes edges hline hboundary
  have hm : 9 ≤ M.card := by omega
  have hs : 129 + deficit + (∑ p ∈ P, holes p) ≤ 6 * M.card + 16 * P.card := by
    rwa [hp]
  have hb := mixed_fibre_deficit_capacity P M holes edges hm hdis deficit loss hs hedges
    hline hboundary
  have hm10 : M.card = 10 := by omega
  exact ⟨hm10, by omega⟩

set_option maxHeartbeats 800000 in
-- The proof elaborates both vertex and edge projections over the four-cube.
open Classical in
open scoped BigOperators in
/-- In the triangle-complement contact geometry with 258 vertices, the
five- and six-pure cases have explicit mixed occupancy and edge budgets. -/
theorem triangle_complement_mixed_fibre_deficits {C D : Finset (Q 9)} (b : Bool)
    (e : Fin 5 ↪ Fin 9) (g : Fin 4 ↪ Fin 9)
    (hcover : ∀ k, k ∉ univ.map e ↔ ∃ i, g i = k)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hinside : ∀ T ∈ minimumDisplacements C D b 2, ¬ T ⊆ univ.map e)
    {j k : Fin 9} (hj : j ∈ univ.map e) (hk : k ∈ univ.map e) (hjk : j ≠ k)
    (hmissing : ∀ i ∉ univ.map e,
      ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2 ∧
      ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hc : BalancedCriticalSpectrum.IsBalanced C) (hd : BalancedCriticalSpectrum.IsBalanced D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsize : C.card + D.card = 258) :
    let bank (S : Finset (Q 9)) (p : Q 4) :=
      (S.filter (fun x => parity x = b)).filter (fun x => (fun i => x (g i)) = p)
    let M := univ.filter (fun p => (bank C p).Nonempty ∧ (bank D p).Nonempty)
    let P := univ.filter (fun p => ((bank C p).Nonempty ∧ bank D p = ∅) ∨
      (bank C p = ∅ ∧ (bank D p).Nonempty))
    let A := univ.map e
    let occ (p : Q 4) := (bank C p).card + (bank D p).card
    let edges (p : Q 4) := (freeEdges C (bank C p) A).card + (freeEdges D (bank D p) A).card
    let deficit := 6 * M.card - ∑ p ∈ M, occ p
    let loss := 15 * M.card - ∑ p ∈ M, edges p
    (P.card = 5 → M.card = 11 ∧ 5 * deficit + loss ≤ 12 ∧ ∀ p ∈ M, 5 ≤ occ p) ∧
      (P.card = 6 → M.card = 10 ∧ 5 * deficit + loss ≤ 41) := by
  intro bank M P A occ edges deficit loss
  let project (x : Q 9) : Q 4 := fun i => x (g i)
  let lift (p : Q 4) (l : Fin 9) : Bool :=
    if h : ∃ i, g i = l then p (Classical.choose h) else false
  let holes (p : Q 4) := 16 - occ p
  have hA : A.card = 5 := by simp [A]
  have hc3 (x : Q 9) (hx : x ∈ C) : (directions C x).card ≤ 3 :=
    (regular_directions C hrC hx).le
  have hd3 (x : Q 9) (hx : x ∈ D) : (directions D x).card ≤ 3 :=
    (regular_directions D hrD hx).le
  have hparCard (S : Finset (Q 9)) :
      (paritySide S b).card = (S.filter (fun x => parity x = b)).card := by
    refine card_bij (s := paritySide S b) (t := S.filter (fun x => parity x = b))
      (fun x _ => x.val) ?_ ?_ ?_
    · intro x hx
      have he : parity x.val = b := (mem_filter.mp hx).2
      exact mem_filter.mpr ⟨x.property, he⟩
    · intro x _ y _ he
      exact Subtype.ext he
    · intro x hx
      obtain ⟨hxS, hxB⟩ := mem_filter.mp hx
      let y : (S : Set (Q 9)) := ⟨x, hxS⟩
      have hy : y ∈ paritySide S b := mem_filter.mpr ⟨mem_univ y, hxB⟩
      exact ⟨y, hy, rfl⟩
  have htotal : 129 ≤ (C.filter (fun x => parity x = b)).card +
      (D.filter (fun x => parity x = b)).card := by
    have ha := regular_parity_card C b (by decide) hrC
    have hb := regular_parity_card D b (by decide) hrD
    rw [hparCard] at ha hb
    omega
  have h43 (i : Fin 9) : directionEdges C i + directionEdges D i = 43 := by
    have hC := direction_edge_count (d := 3) C hrC hc i
    have hD := direction_edge_count (d := 3) D hrD hd i
    omega
  have hedges : 215 ≤ (freeEdges C (C.filter (fun x => parity x = b)) A).card +
      (freeEdges D (D.filter (fun x => parity x = b)) A).card := by
    rw [freeEdges_eq_sum_directionEdges, freeEdges_eq_sum_directionEdges, ← sum_add_distrib]
    simp [h43, hA]
  have hout (i : Fin 4) : g i ∉ A := (hcover _).mpr ⟨i, rfl⟩
  have hcoord (p : Q 4) (i : Fin 4) : lift p (g i) = p i := by
    have hi : ∃ j, g j = g i := ⟨i, rfl⟩
    change (if h : ∃ j, g j = g i then p (Classical.choose h) else false) = p i
    rw [dif_pos hi, g.injective (Classical.choose_spec hi)]
  have hproj (p : Q 4) : project (lift p) = p := funext (hcoord p)
  have hbank (S : Finset (Q 9)) (x : Q 9) :
      bank S (project x) = (restrictToFibre S A x).filter (fun y => parity y = b) := by
    ext y
    have h : project y = project x ↔ sameFibre A x y := by
      constructor
      · intro he l hl
        obtain ⟨i, rfl⟩ := (hcover l).mp hl
        exact congrFun he i
      · intro he
        exact funext (fun i => he (g i) (hout i))
    simp only [bank, restrictToFibre, mem_filter]
    change (_ ∧ project y = project x) ↔ _
    rw [h]
    tauto
  have hrepr (S : Finset (Q 9)) (p : Q 4) :
      bank S p = (restrictToFibre S A (lift p)).filter (fun y => parity y = b) := by
    simpa only [hproj] using hbank S (lift p)
  have hflip (p : Q 4) (i : Fin 4) :
      project (flip (lift p) (g i)) = flip p i := by
    funext l
    by_cases hl : l = i
    · subst l
      simp [project, hcoord]
    · simp [project, BalancedCriticalSpectrum.flip, hl, g.injective.ne hl, hcoord]
  have hfibre (p : Q 4) : (bank univ p).card ≤ 16 := by
    have h := Q9InactiveContactFibre.adjacent_fibre_capacity (C := ∅) (D := univ) b
      (flip (lift p) (g 0)) e (hout 0) ∅ (empty_subset _) (by simp)
    rw [hrepr]
    simpa using h
  have hbankC (S : Finset (Q 9)) (p : Q 4) : (bank S p).card ≤ 16 := by
    have hs : bank S p ⊆ bank univ p := by
      intro x hx
      obtain ⟨hxS, hxp⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hxS).2⟩, hxp⟩
    exact (card_le_card hs).trans (hfibre p)
  have htally (S : Finset (Q 9)) :
      (S.filter (fun x => parity x = b)).card = ∑ p, (bank S p).card :=
    card_eq_sum_card_fiberwise (f := project) (fun _ _ => mem_univ _)
  have hedgetally (S : Finset (Q 9)) :
      (freeEdges S (S.filter (fun x => parity x = b)) A).card =
        ∑ p, (freeEdges S (bank S p) A).card := by
    rw [card_eq_sum_card_fiberwise (f := fun v : Q 9 × Fin 9 => project v.1)
      (t := (univ : Finset (Q 4))) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro p _
    congr 1
    ext v
    constructor
    · intro h
      obtain ⟨hv, hp⟩ := mem_filter.mp h
      obtain ⟨hpair, he⟩ := mem_filter.mp hv
      obtain ⟨hs, ha⟩ := mem_product.mp hpair
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hs, hp⟩, ha⟩, he⟩
    · intro h
      obtain ⟨hpair, he⟩ := mem_filter.mp h
      obtain ⟨hv, ha⟩ := mem_product.mp hpair
      obtain ⟨hs, hp⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hs, ha⟩, he⟩, hp⟩
  rw [htally C, htally D, ← sum_add_distrib] at htotal
  rw [hedgetally C, hedgetally D, ← sum_add_distrib] at hedges
  change 129 ≤ ∑ p, occ p at htotal
  change 215 ≤ ∑ p, edges p at hedges
  have hmixed := (Q9InactiveContactFibre.five_axis_fibre_counts b e g hcover hsep
    hinside hj hk hjk hmissing (by rw [htally C, htally D, ← sum_add_distrib]; exact htotal)).1
  change M.card ≤ 11 at hmixed
  have hdis : Disjoint P M := disjoint_left.mpr (by
    intro p hp hm
    have hm' := (mem_filter.mp hm).2
    rcases (mem_filter.mp hp).2 with hp' | hp'
    · exact hm'.2.ne_empty hp'.2
    · exact hm'.1.ne_empty hp'.1)
  have hparts (f : Q 4 → ℕ) (hzero : ∀ p,
      bank C p = ∅ → bank D p = ∅ → f p = 0) :
      (∑ p, f p) = (∑ p ∈ M, f p) + ∑ p ∈ P, f p := by
    rw [← sum_union hdis.symm]
    symm
    apply sum_subset (subset_univ _)
    intro p _ hp
    have hnM : p ∉ M := fun hm => hp (mem_union_left _ hm)
    have hnP : p ∉ P := fun hh => hp (mem_union_right _ hh)
    apply hzero
    · by_contra he
      by_cases hD : bank D p = ∅
      · exact hnP (mem_filter.mpr ⟨mem_univ _, Or.inl ⟨nonempty_iff_ne_empty.mpr he, hD⟩⟩)
      · exact hnM (mem_filter.mpr ⟨mem_univ _, nonempty_iff_ne_empty.mpr he,
          nonempty_iff_ne_empty.mpr hD⟩)
    · by_contra he
      by_cases hC : bank C p = ∅
      · exact hnP (mem_filter.mpr ⟨mem_univ _, Or.inr ⟨hC, nonempty_iff_ne_empty.mpr he⟩⟩)
      · exact hnM (mem_filter.mpr ⟨mem_univ _, nonempty_iff_ne_empty.mpr hC,
          nonempty_iff_ne_empty.mpr he⟩)
  rw [hparts occ (by intro p hC hD; simp [occ, hC, hD])] at htotal
  rw [hparts edges (by intro p hC hD; simp [edges, freeEdges, hC, hD])] at hedges
  have hmoccOne (p : Q 4) (hp : p ∈ M) : occ p ≤ 6 := by
    obtain ⟨ha, hD⟩ := (mem_filter.mp hp).2
    rw [hrepr] at ha hD
    change (bank C p).card + (bank D p).card ≤ 6
    rw [hrepr C, hrepr D]
    exact Q9InactiveContactFibre.mixed_five_axis_fibre_capacity b (lift p) e hsep hinside ha hD
  have hmedgeOne (p : Q 4) (hp : p ∈ M) : edges p ≤ 15 := by
    obtain ⟨ha, hD⟩ := (mem_filter.mp hp).2
    rw [hrepr] at ha hD
    change (freeEdges C (bank C p) A).card + (freeEdges D (bank D p) A).card ≤ 15
    rw [hrepr C, hrepr D]
    exact Q9InactiveContactFibre.mixed_five_axis_fibre_edge_capacity b (lift p) e hsep
      hinside hc hd hc3 hd3 ha hD
  have hmocc : (∑ p ∈ M, occ p) ≤ 6 * M.card := by
    simpa [Nat.mul_comm] using sum_le_sum hmoccOne
  have hmedges : (∑ p ∈ M, edges p) ≤ 15 * M.card := by
    simpa [Nat.mul_comm] using sum_le_sum hmedgeOne
  have hone (S T : Finset (Q 9)) (p : Q 4) (i : Fin 4)
      (hmj : ({g i, j} : Finset (Fin 9)) ∉ minimumDisplacements S T b 2)
      (hmk : ({g i, k} : Finset (Fin 9)) ∉ minimumDisplacements S T b 2)
      (hs : (bank S (flip p i)).Nonempty) : (bank T p).card ≤ 14 := by
    rw [← hflip p i, hbank S] at hs
    rw [hrepr T]
    simpa using Q9InactiveContactFibre.adjacent_fibre_two_holes b (flip (lift p) (g i)) e
      (hout i) hj hk hjk hmj hmk hs
  have hnear (p : Q 4) (hp : p ∈ P) (i : Fin 4) (hm : flip p i ∈ M) : 2 ≤ holes p := by
    obtain ⟨hmC, hmD⟩ := (mem_filter.mp hm).2
    have hab := hmissing _ (hout i)
    rcases (mem_filter.mp hp).2 with hp' | hp'
    · rw [minimumDisplacements_swap_two C D b] at hab
      have h := hone D C p i hab.1 hab.2 hmD
      simp only [holes, occ, hp'.2, card_empty, Nat.add_zero]
      omega
    · have h := hone C D p i hab.1 hab.2 hmC
      simp only [holes, occ, hp'.1, card_empty, Nat.zero_add]
      omega
  have hslots (p : Q 4) (hp : p ∈ P) : occ p ≤ 16 := by
    rcases (mem_filter.mp hp).2 with hp' | hp'
    · simpa [occ, hp'.2] using hbankC C p
    · simpa [occ, hp'.1] using hbankC D p
  have hhole : (∑ p ∈ P, holes p) + (∑ p ∈ P, occ p) = 16 * P.card := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ p ∈ P, 16 := sum_congr rfl (by
        intro p hp
        exact Nat.sub_add_cancel (hslots p hp))
      _ = _ := by simp [Nat.mul_comm]
  have hsmallBank (S : Finset (Q 9)) (p : Q 4)
      (h3 : ∀ x ∈ S, (directions S x).card ≤ 3)
      (hsmall : 16 - (bank S p).card ≤ 3) :
      (freeEdges S (bank S p) A).card ≤ 6 * (16 - (bank S p).card - 1) := by
    let H := (restrictToFibre univ A (lift p)).filter (fun x => parity x = b ∧ x ∉ S)
    have hparts : (bank univ p).filter (fun x => x ∈ S) = bank S p := by
      ext x
      simp [bank]
      tauto
    have hnot : (bank univ p).filter (fun x => x ∉ S) = H := by
      rw [hrepr]
      ext x
      simp [H, restrictToFibre]
      tauto
    have hsum := card_filter_add_card_filter_not (s := bank univ p) (fun x => x ∈ S)
    rw [hparts, hnot] at hsum
    have hcap := hfibre p
    have hH : H.card ≤ 16 - (bank S p).card := by omega
    have hf := few_holes_bound_freeEdges S A hA (lift p) b h3 (hH.trans hsmall)
    change (freeEdges S ((restrictToFibre S A (lift p)).filter _) A).card ≤ 6 * (H.card - 1) at hf
    rw [← hrepr S p] at hf
    exact hf.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hH _))
  have hdegBank (S : Finset (Q 9)) (p : Q 4) (h3 : ∀ x ∈ S, (directions S x).card ≤ 3) :
      (freeEdges S (bank S p) A).card ≤ 3 * (bank S p).card :=
    freeEdges_le_degree_sum (fun x hx => h3 x (mem_filter.mp (mem_filter.mp hx).1).1)
  have hsmall (p : Q 4) (hp : p ∈ P) (hh : holes p ≤ 3) : edges p ≤ 6 * (holes p - 1) := by
    rcases (mem_filter.mp hp).2 with hp' | hp'
    · simpa [edges, holes, occ, freeEdges, hp'.2] using
        hsmallBank C p hc3 (by simpa [holes, occ, hp'.2] using hh)
    · simpa [edges, holes, occ, freeEdges, hp'.1] using
        hsmallBank D p hd3 (by simpa [holes, occ, hp'.1] using hh)
  have hdeg (p : Q 4) (hp : p ∈ P) : edges p ≤ 3 * (16 - holes p) := by
    have hr : 16 - holes p = occ p := by have := hslots p hp; simp only [holes]; omega
    rw [hr]
    rcases (mem_filter.mp hp).2 with hp' | hp'
    · simpa [edges, occ, freeEdges, hp'.2] using hdegBank C p hc3
    · simpa [edges, occ, freeEdges, hp'.1] using hdegBank D p hd3
  have hoccupancy :
      129 + deficit + (∑ p ∈ P, holes p) ≤ 6 * M.card + 16 * P.card := by
    have hfill := Nat.sub_add_cancel hmocc
    change deficit + (∑ p ∈ M, occ p) = 6 * M.card at hfill
    omega
  have hbudget : 215 + loss ≤ 15 * M.card + ∑ p ∈ P, edges p := by
    have hfill := Nat.sub_add_cancel hmedges
    change loss + (∑ p ∈ M, edges p) = 15 * M.card at hfill
    omega
  have hholes (S : Finset (Q 9)) (p : Q 4) (z : Q 9) (hz : project z = p) :
      ((restrictToFibre univ A z).filter (fun x => parity x = b ∧ x ∉ S)).card ≤
        16 - (bank S p).card := by
    let H := (restrictToFibre univ A z).filter (fun x => parity x = b ∧ x ∉ S)
    have hS : (bank univ p).filter (fun x => x ∈ S) = bank S p := by
      ext x
      simp [bank]
      tauto
    have hH : (bank univ p).filter (fun x => x ∉ S) = H := by
      rw [← hz, hbank]
      ext x
      simp [H, restrictToFibre]
      tauto
    have hsum := card_filter_add_card_filter_not (s := bank univ p) (fun x => x ∈ S)
    rw [hS, hH] at hsum
    have hcap := hfibre p
    change H.card ≤ 16 - (bank S p).card
    omega
  have hlineBank (S : Finset (Q 9)) (p : Q 4) (hbal : BalancedCriticalSpectrum.IsBalanced S)
      (hdeg : ∀ x ∈ S, (directions S x).card ≤ 3) :
      (freeEdges S (bank S p) A).card ≤ 5 * (16 - (bank S p).card) + 1 := by
    have h := (five_axis_hole_linear_bound S e (hout 0) (lift p) b hbal hdeg).1
    change (freeEdges S ((restrictToFibre S A (lift p)).filter _) A).card ≤
      5 * ((restrictToFibre univ A (lift p)).filter _).card + 1 at h
    rw [← hrepr] at h
    have hh := hholes S p (lift p) (hproj p)
    omega
  have hline (p : Q 4) (hp : p ∈ P) : edges p ≤ 5 * holes p + 1 := by
    rcases (mem_filter.mp hp).2 with hp' | hp'
    · simpa [edges, holes, occ, freeEdges, hp'.2] using hlineBank C p hc hc3
    · simpa [edges, holes, occ, freeEdges, hp'.1] using hlineBank D p hd hd3
  have hboundBank (S T : Finset (Q 9)) (p : Q 4) (q : Fin 4)
      (hST : ∀ x ∈ S, ∀ y ∈ T, 2 ≤ hammingDist x y)
      (hbal : BalancedCriticalSpectrum.IsBalanced T)
      (hdeg : ∀ x ∈ T, (directions T x).card ≤ 3)
      (hmj : ({g q, j} : Finset (Fin 9)) ∉ minimumDisplacements S T b 2)
      (hmk : ({g q, k} : Finset (Fin 9)) ∉ minimumDisplacements S T b 2)
      (hs : (bank S (flip p q)).Nonempty) :
      (freeEdges T (bank T p) A).card + 6 ≤ 5 * (16 - (bank T p).card) := by
    obtain ⟨x, hx⟩ := hs
    obtain ⟨hxp, hxq⟩ := mem_filter.mp hx
    obtain ⟨hxS, hxb⟩ := mem_filter.mp hxp
    have hprojFlip : project (BalancedCriticalSpectrum.flip x (g q)) = p := by
      funext l
      have hcoord := congrFun hxq l
      change x (g l) = flip p q l at hcoord
      by_cases hl : l = q
      · subst l
        simpa [project] using congrArg Bool.not hcoord
      · simpa [project, BalancedCriticalSpectrum.flip, hl, g.injective.ne hl] using hcoord
    have hb := adjacent_fibre_hole_edge_capacity b hxS hxb hST e (hout q)
      hj hk hjk hmj hmk hbal hdeg
    change (freeEdges T ((restrictToFibre T A (BalancedCriticalSpectrum.flip x (g q))).filter _) A).card + 6 ≤
      5 * ((restrictToFibre univ A (BalancedCriticalSpectrum.flip x (g q))).filter _).card at hb
    have hh := hholes T p (BalancedCriticalSpectrum.flip x (g q)) hprojFlip
    rw [← hbank, hprojFlip] at hb
    omega
  have hboundary (p : Q 4) (hp : p ∈ P)
      (hm : ∃ i : Fin 4, flip p i ∈ M) : edges p + 6 ≤ 5 * holes p := by
    obtain ⟨i, hi⟩ := hm
    obtain ⟨hmC, hmD⟩ := (mem_filter.mp hi).2
    have hfs := hmissing _ (hout i)
    rcases (mem_filter.mp hp).2 with hp' | hp'
    · rw [minimumDisplacements_swap_two C D b] at hfs
      have hsep' (x : Q 9) (hx : x ∈ D) (y : Q 9) (hy : y ∈ C) :
          2 ≤ hammingDist x y := by rw [hammingDist_comm]; exact hsep y hy x hx
      simpa [edges, holes, occ, freeEdges, hp'.2] using
        hboundBank D C p i hsep' hc hc3 hfs.1 hfs.2 hmD
    · simpa [edges, holes, occ, freeEdges, hp'.1] using
        hboundBank C D p i hsep hd hd3 hfs.1 hfs.2 hmC
  constructor
  · intro hpure
    have hm11 := five_pure_forces_eleven_mixed P M holes edges hpure hmixed hdis hnear
      (by omega) (by omega) hsmall hdeg
    have h := mixed_fibre_deficit_capacity P M holes edges (by omega) hdis deficit loss
      hoccupancy hbudget hline hboundary
    have hw : 5 * deficit + loss ≤ 12 := by omega
    refine ⟨hm11, hw, ?_⟩
    intro p hp
    have hd1 : 6 - occ p ≤ deficit := by
      have he : (∑ q ∈ M, (6 - occ q)) = deficit := by
        rw [Finset.sum_tsub_distrib _ hmoccOne]
        simp [deficit, Nat.mul_comm]
      rw [← he]
      exact single_le_sum (fun q _ => Nat.zero_le (6 - occ q)) hp
    have hl1 : 15 - edges p ≤ loss := by
      have he : (∑ q ∈ M, (15 - edges q)) = loss := by
        rw [Finset.sum_tsub_distrib _ hmedgeOne]
        simp [loss, Nat.mul_comm]
      rw [← he]
      exact single_le_sum (fun q _ => Nat.zero_le (15 - edges q)) hp
    have hcdeg := hdegBank C p hc3
    have hddeg := hdegBank D p hd3
    change _ ≤ 3 * (bank C p).card at hcdeg
    change _ ≤ 3 * (bank D p).card at hddeg
    have hedge : edges p ≤ 3 * occ p := by dsimp [edges, occ]; omega
    omega
  · intro hpure
    exact six_pure_fibre_capacity P M holes edges hpure hdis deficit loss
      (by simpa [hpure] using hoccupancy) hbudget hline hboundary

open Classical in
open scoped BigOperators in
/-- For the triangle-complement contact geometry, the global free edge count
forces every fibre outside the five occupied pure fibres to be mixed. -/
theorem five_pure_contact_fibres_force_eleven_mixed {C D : Finset (Q 9)} (b : Bool)
    (e : Fin 5 ↪ Fin 9) (g : Fin 4 ↪ Fin 9)
    (hcover : ∀ k, k ∉ univ.map e ↔ ∃ i, g i = k)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hinside : ∀ T ∈ minimumDisplacements C D b 2, ¬ T ⊆ univ.map e)
    {j k : Fin 9} (hj : j ∈ univ.map e) (hk : k ∈ univ.map e) (hjk : j ≠ k)
    (hmissing : ∀ i ∉ univ.map e,
      ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2 ∧
      ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hc : BalancedCriticalSpectrum.IsBalanced C) (hd : BalancedCriticalSpectrum.IsBalanced D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsize : C.card + D.card = 258) :
    let bank (S : Finset (Q 9)) (p : Q 4) :=
      (S.filter (fun x => parity x = b)).filter (fun x => (fun i => x (g i)) = p)
    let M := univ.filter (fun p => (bank C p).Nonempty ∧ (bank D p).Nonempty)
    let P := univ.filter (fun p => ((bank C p).Nonempty ∧ bank D p = ∅) ∨
      (bank C p = ∅ ∧ (bank D p).Nonempty))
    P.card = 5 → M.card = 11 := by
  exact fun hp => ((triangle_complement_mixed_fibre_deficits b e g hcover hsep
    hinside hj hk hjk hmissing hc hd hrC hrD hsize).1 hp).1

#print axioms triangle_complement_mixed_fibre_deficits
#print axioms mixed_fibre_deficit_capacity
#print axioms six_pure_fibre_capacity
#print axioms adjacent_fibre_hole_edge_capacity
#print axioms adjacent_fibre_small_hole_edge_capacity
#print axioms few_holes_bound_freeEdges
#print axioms pure_edge_budget
#print axioms parity_cut_edge_square_le
#print axioms five_axis_hole_energy
#print axioms five_axis_hole_linear_bound
#print axioms five_pure_forces_eleven_mixed
#print axioms five_pure_contact_fibres_force_eleven_mixed

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PureFibreEdgeCapacity
