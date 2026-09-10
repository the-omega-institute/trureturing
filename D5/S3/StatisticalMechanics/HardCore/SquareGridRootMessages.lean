/- GID: D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/SquareGridRootMessages
   mirror-E: none(waiver:exact-four-child-root-correspondence)
   anchors: []
   digest: The existing four-direction root domains exactly realize actual partition recursion. -/

import D5.S3.StatisticalMechanics.HardCore.SquareGridMessages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.SquareGridRootMessages

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
open D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.StatisticalMechanics.HardCore.SquareGridMessages
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates

/-- Public equivalence realizing the existing rootDomain's internal frame.
Its agreement with that existing domain is proved below, without referring to
private declaration names or replacing the original domain definition. -/
def rootFrame (e : Fin 4) : Point ≃ Point where
  toFun p := if e = 0 then (p.1 - 1, p.2) else if e = 1 then (-p.2 - 1, p.1)
    else if e = 2 then (p.2 - 1, -p.1) else (-p.1 - 1, -p.2)
  invFun p := if e = 0 then (p.1 + 1, p.2) else if e = 1 then (p.2, -p.1 - 1)
    else if e = 2 then (-p.2, p.1 + 1) else (-p.1 - 1, -p.2)
  left_inv := by intro p; fin_cases e <;> ext <;> simp <;> omega
  right_inv := by intro p; fin_cases e <;> ext <;> simp <;> omega

/-- The actual four root frames preserve and reflect grid adjacency. -/
theorem root_frame_adj_iff (e : Fin 4) (p q : Point) :
    squareGrid.Adj (rootFrame e p) (rootFrame e q) ↔ squareGrid.Adj p q := by
  fin_cases e <;> simp [rootFrame, squareGrid] <;> omega

private def fullOrder : List (Fin 4) := [0, 1, 2, 3]
/-- Ordered root neighbors deleted before the selected first child. -/
def rootEarlier (e : Fin 4) : List Point := (fullOrder.take e.val).map rootDirection

private theorem root_table :
    (∀ e : Fin 4, (rootEarlier e).toFinset =
      (Finset.univ.filter fun j : Fin 4 => j < e).image rootDirection) ∧
    (∀ e : Fin 4, rootFrame e (rootDirection e) = (0, 0) ∧
      rootFrame e (0, 0) = (-1, 0) ∧ rootDirection e ∉ (rootEarlier e).toFinset) ∧
    (fullOrder.map rootDirection).toFinset = {(1, 0), (0, -1), (0, 1), (-1, 0)} := by
  decide +kernel

private theorem root_domain_frame (V : Finset Point) (e : Fin 4) :
    rootDomain V e = (afterErases (V.erase (0, 0)) (rootEarlier e)).image (rootFrame e) := by
  change ((V \ insert (0, 0)
    ((Finset.univ.filter fun j : Fin 4 => j < e).image rootDirection)).image
      (rootFrame e)) = _
  rw [afterErases_eq_sdiff, root_table.1 e]
  congr 1
  ext p
  simp <;> tauto

/-- The four existing rootDomain objects carry exactly the successive actual
neighbor vacancy factors after moving the selected root neighbor to the origin. -/
theorem root_child_vacancy {K : Type*} [Field K]
    (V : Finset Point) (e : Fin 4) (z : K) :
    gridVacancy (rootDomain V e) (0, 0) z =
      gridVacancy (afterErases (V.erase (0, 0)) (rootEarlier e)) (rootDirection e) z := by
  rw [root_domain_frame]
  have he := image_erase_equiv (rootFrame e)
    (afterErases (V.erase (0, 0)) (rootEarlier e)) (rootDirection e)
  rw [(root_table.2.1 e).1] at he
  unfold gridVacancy
  rw [← he]
  unfold gridPartition
  rw [partition_relabel squareGrid squareGrid (rootFrame e) (root_frame_adj_iff e),
    partition_relabel squareGrid squareGrid (rootFrame e) (root_frame_adj_iff e)]

private theorem root_product {K : Type*} [Field K] (V : Finset Point) (z : K) :
    vacancyProduct squareGrid (fun _ => z) (V.erase (0, 0)) (fullOrder.map rootDirection) =
      ∏ e : Fin 4, gridVacancy (rootDomain V e) (0, 0) z := by
  rw [Fin.prod_univ_four]
  simp_rw [root_child_vacancy]
  simp [fullOrder, rootEarlier, vacancyProduct, afterErases, gridVacancy] <;> ring

private theorem root_terminal (V : Finset Point) :
    afterErases (V.erase (0, 0)) (fullOrder.map rootDirection) =
      closedComplement squareGrid V (0, 0) := by
  rw [afterErases_eq_sdiff, root_table.2.2]
  ext p
  rcases p with ⟨x, y⟩
  simp [closedComplement, squareGrid] <;> omega

/-- The unconditioned four-neighbor root is identified with the actual
independent-set partition. Only proper pre-recentered domains are assumed
nonzero. No three-child contraction is incorrectly imposed on the root. -/
theorem root_partition_recursion {K : Type*} [Field K]
    (V : Finset Point) (h0 : (0, 0) ∈ V) (z : K)
    (hproper : ∀ U : Finset Point, U ⊆ V.erase (0, 0) → gridPartition U z ≠ 0) :
    gridPartition V z = gridPartition (V.erase (0, 0)) z *
      (1 + z * ∏ e : Fin 4, gridVacancy (rootDomain V e) (0, 0) z) := by
  have ht := grid_vacancy_product_telescopes (V.erase (0, 0))
    (fullOrder.map rootDirection) z hproper
  rw [root_terminal, root_product] at ht
  have hn := hproper (V.erase (0, 0)) (by intro p hp; exact hp)
  calc
    _ = gridPartition (V.erase (0, 0)) z +
        z * gridPartition (closedComplement squareGrid V (0, 0)) z :=
      partition_delete squareGrid V (0, 0) h0 (fun _ => z)
    _ = _ := by rw [ht]; field_simp [hn]

/-- Every present first child is a smaller, origin-rooted instance compatible
with the existing initial geometric type zero. Extra earlier-neighbor deletions
remain in the actual domain even though type zero records only the parent. -/
theorem root_child_context (V : Finset Point) (h0 : (0, 0) ∈ V)
    (e : Fin 4) (he : rootDirection e ∈ V) :
    (0, 0) ∈ rootDomain V e ∧ Disjoint (rootDomain V e) (radiusFourMask 0) ∧
      (rootDomain V e).card < V.card := by
  have hd : rootDirection e ≠ (0, 0) := by fin_cases e <;> decide
  have hs : afterErases (V.erase (0, 0)) (rootEarlier e) ⊆ V.erase (0, 0) := by
    rw [afterErases_eq_sdiff]
    exact Finset.sdiff_subset
  have hne : (0, 0) ∉ afterErases (V.erase (0, 0)) (rootEarlier e) := by
    intro h
    exact Finset.notMem_erase (0, 0) V (hs h)
  rw [root_domain_frame]
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨rootDirection e, ?_, (root_table.2.1 e).1⟩
    rw [afterErases_eq_sdiff]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_erase.mpr ⟨hd, he⟩, (root_table.2.1 e).2.2⟩
  · rw [radiusFour_geometry.2.2.1]
    apply Finset.disjoint_left.mpr
    intro p hp hm
    have hpEq : p = (-1, 0) := Finset.mem_singleton.mp hm
    rcases Finset.mem_image.mp hp with ⟨q, hq, hqEq⟩
    have hq0 := (rootFrame e).injective (hqEq.trans
      (hpEq.trans (root_table.2.1 e).2.1.symm))
    exact hne (hq0 ▸ hq)
  · have hi : ((afterErases (V.erase (0, 0)) (rootEarlier e)).image (rootFrame e)).card ≤
        (afterErases (V.erase (0, 0)) (rootEarlier e)).card := Finset.card_image_le
    have hcard := Finset.card_le_card hs
    have herase := Finset.card_erase_of_mem h0
    have hpos : 0 < V.card := Finset.card_pos.mpr ⟨(0, 0), h0⟩
    omega

#print axioms root_frame_adj_iff
#print axioms root_child_vacancy
#print axioms root_partition_recursion
#print axioms root_child_context

end D5.S3.StatisticalMechanics.HardCore.SquareGridRootMessages
