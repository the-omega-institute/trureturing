/- GID: D5/S3/StatisticalMechanics/HardCore/SquareGridMessages
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/SquareGridMessages
   mirror-E: none(waiver:exact-actual-subgraph-type-correspondence)
   anchors: []
   digest: Actual ordered grid subgraphs realize the certified typed vacancy recursion. -/

import D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import D5.S3.StatisticalMechanics.HardCore.RealPartitionMessages
import D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.SquareGridMessages

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion
open D5.S3.StatisticalMechanics.HardCore.RealPartitionMessages
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates
open D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessages

/-- The six orders, matching the existing position table exactly. -/
def neighborOrder (a : Fin 6) : List (Fin 3) :=
  if a = 0 then [0, 1, 2] else if a = 1 then [0, 2, 1]
  else if a = 2 then [1, 0, 2] else if a = 3 then [1, 2, 0]
  else if a = 4 then [2, 0, 1] else [2, 1, 0]

private def «prefix» (a : Fin 6) (d : Fin 3) : List Point :=
  (0, 0) :: ((neighborOrder a).take (position a d)).map direction

private theorem order_geometry :
    (∀ a : Fin 6, ((neighborOrder a).map direction).toFinset =
      {(1, 0), (0, -1), (0, 1)}) ∧
    (∀ (a : Fin 6) (d : Fin 3), («prefix» a d).toFinset = deleted a d) ∧
    (∀ (a : Fin 6) (d : Fin 3), direction d ∉ deleted a d) := by
  decide +kernel

private theorem before_eq_prefix (V : Finset Point) (a : Fin 6) (d : Fin 3) :
    V \ deleted a d = afterErases V («prefix» a d) := by
  rw [afterErases_eq_sdiff, order_geometry.2.1 a d]

/-- The child value is a ratio of actual independent-set sums on the exact
existing advance domain. No finite-tree message is substituted for this ratio. -/
def childVacancy {K : Type*} [Field K]
    (V : Finset Point) (a : Fin 6) (d : Fin 3) (z : K) : K :=
  gridVacancy (advance V a d) (0, 0) z

/-- Exact identification with the successive unrotated deletion-domain ratio.
Both marked partitions are transported by the actual grid coordinate map. -/
theorem child_vacancy_before {K : Type*} [Field K]
    (V : Finset Point) (a : Fin 6) (d : Fin 3) (z : K) :
    childVacancy V a d z = gridVacancy (V \ deleted a d) (direction d) z := by
  simpa only [childVacancy, advance, recenter_direction] using
    vacancy_recenter (V \ deleted a d) (direction d) d z

/-- Ordered elimination uses exactly the three geometric child values, with
all multiplicities and the successive domains preserved. This algebraic
identity itself holds even if a field denominator is zero. -/
theorem ordered_product_children {K : Type*} [Field K]
    (V : Finset Point) (a : Fin 6) (z : K) :
    vacancyProduct squareGrid (fun _ => z) (V.erase (0, 0))
        ((neighborOrder a).map direction) = ∏ d, childVacancy V a d z := by
  rw [Fin.prod_univ_three]
  simp_rw [child_vacancy_before, before_eq_prefix]
  fin_cases a <;>
    simp [neighborOrder, «prefix», position, direction, vacancyProduct, afterErases,
      gridVacancy] <;> ring

private theorem origin_neighbors (p : Point) :
    squareGrid.Adj (0, 0) p ↔
      p = (1, 0) ∨ p = (-1, 0) ∨ p = (0, 1) ∨ p = (0, -1) := by
  rcases p with ⟨x, y⟩
  simp [squareGrid] <;> omega

private theorem terminal_domain (V : Finset Point) (hp : (-1, 0) ∉ V) (a : Fin 6) :
    afterErases (V.erase (0, 0)) ((neighborOrder a).map direction) =
      closedComplement squareGrid V (0, 0) := by
  rw [afterErases_eq_sdiff, order_geometry.1 a]
  ext p
  by_cases hv : p ∈ V
  · have hpw : p ≠ (-1, 0) := by intro h; subst p; exact hp hv
    simp [closedComplement, origin_neighbors, hv, hpw] <;> tauto
  · simp [closedComplement, hv]

/-- Proper-domain nonvanishing gives the exact ordered vacancy quotient. -/
theorem grid_vacancy_product_telescopes {K : Type*} [Field K]
    (V : Finset Point) (l : List Point) (z : K)
    (hV : ∀ U : Finset Point, U ⊆ V → gridPartition U z ≠ 0) :
    vacancyProduct squareGrid (fun _ => z) V l =
      gridPartition (afterErases V l) z / gridPartition V z := by
  induction l generalizing V with
  | nil => simp [vacancyProduct, afterErases, hV V (by intro p hp; exact hp)]
  | cons v l ih =>
      have he : ∀ U : Finset Point, U ⊆ V.erase v → gridPartition U z ≠ 0 := by
        intro U hU
        exact hV U (hU.trans (Finset.erase_subset v V))
      simp only [vacancyProduct, afterErases]
      rw [ih (V.erase v) he]
      have h0 := hV V (by intro p hp; exact hp)
      have h1 := he (V.erase v) (by intro p hp; exact hp)
      field_simp [h0, h1] <;> ring

/-- Exact finite-grid recurrence over any field, with hypotheses confined to
proper subsets before recentering. The target partition is not assumed nonzero.
The three actual child domains are those used by the geometric controller. -/
theorem grid_partition_recursion {K : Type*} [Field K]
    (V : Finset Point) (h0 : (0, 0) ∈ V) (hp : (-1, 0) ∉ V)
    (a : Fin 6) (z : K)
    (hproper : ∀ U : Finset Point, U ⊆ V.erase (0, 0) → gridPartition U z ≠ 0) :
    gridPartition V z = gridPartition (V.erase (0, 0)) z *
      (1 + z * ∏ d, childVacancy V a d z) := by
  have ht := grid_vacancy_product_telescopes (V.erase (0, 0)) ((neighborOrder a).map direction) z hproper
  rw [terminal_domain V hp a, ordered_product_children V a z] at ht
  have hne := hproper (V.erase (0, 0)) (by intro p hp; exact hp)
  calc
    _ = gridPartition (V.erase (0, 0)) z +
        z * gridPartition (closedComplement squareGrid V (0, 0)) z :=
      partition_delete squareGrid V (0, 0) h0 (fun _ => z)
    _ = _ := by rw [ht]; field_simp [hne]

/-- The actual real parent vacancy equals the reciprocal product recursion.
All nonzero hypotheses are derived from nonnegative independent-set weights. -/
theorem grid_real_recursion (V : Finset Point) (h0 : (0, 0) ∈ V)
    (hp : (-1, 0) ∉ V) (a : Fin 6) («λ» : ℝ) («hλ» : 0 ≤ «λ») :
    gridVacancy V (0, 0) «λ» = (1 + «λ» * ∏ d, childVacancy V a d «λ»)⁻¹ := by
  have hn (U : Finset Point) : gridPartition U «λ» ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_partition squareGrid U (fun _ => «λ») (fun _ _ => «hλ»)))
  have he := grid_partition_recursion V h0 hp a «λ» (fun U _ => hn U)
  have hd : 1 + «λ» * ∏ d, childVacancy V a d «λ» ≠ 0 := by
    intro hd
    exact hn V (by simpa [hd] using he)
  unfold gridVacancy
  rw [he]
  field_simp [hn (V.erase (0, 0)), hd]

/-- An absent actual neighbor gives the neutral child value one, not an
arbitrary boundary value. This follows from its two identical positive partitions. -/
theorem child_vacancy_absent (V : Finset Point) (a : Fin 6) (d : Fin 3)
    (hd : direction d ∉ V) («λ» : ℝ) («hλ» : 0 ≤ «λ») : childVacancy V a d «λ» = 1 := by
  rw [child_vacancy_before]
  have hnot : direction d ∉ V \ deleted a d := fun h => hd (Finset.mem_sdiff.mp h).1
  have hn : gridPartition (V \ deleted a d) «λ» ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_partition squareGrid _ (fun _ => «λ») (fun _ _ => «hλ»)))
  simp [gridVacancy, Finset.erase_eq_of_notMem hnot, hn]

/-- The actual finite-domain pruning subset of nonparent directions. -/
def availableDirections (V : Finset Point) : Finset (Fin 3) :=
  Finset.univ.filter fun d => direction d ∈ V

/-- Every available real child has its exact certified successor type,
contains its new origin, remains compatible with that type's blockers, and
has strictly fewer vertices. There is no table-coverage premise here. -/
theorem typed_child_context (V : Finset Point) (i : Fin 881)
    (h0 : (0, 0) ∈ V) (hdis : Disjoint V (radiusFourMask i))
    (d : Fin 3) (hd : direction d ∈ V) :
    ∃ j : Fin 881, radiusFourStep i (radiusFourChoice i) d = some j ∧
      (0, 0) ∈ advance V (radiusFourChoice i) d ∧
      Disjoint (advance V (radiusFourChoice i) d) (radiusFourMask j) ∧
      (advance V (radiusFourChoice i) d).card < V.card := by
  have hg := radiusFour_geometry.2.2.2.2 i d
  cases hs : radiusFourStep i (radiusFourChoice i) d with
  | none =>
      rw [hs] at hg
      exact False.elim ((Finset.disjoint_left.mp hdis) hd hg)
  | some j =>
      rw [hs] at hg
      refine ⟨j, rfl, ?_, ?_, advance_card_lt V h0 (radiusFourChoice i) d⟩
      · exact Finset.mem_image.mpr ⟨direction d,
          Finset.mem_sdiff.mpr ⟨hd, order_geometry.2.2 (radiusFourChoice i) d⟩,
          recenter_direction d⟩
      · rw [hg.2]
        exact advance_disjoint_memoryStep 4 V (radiusFourMask i) (radiusFourChoice i) d hdis

/-- The existing typed affine row inequality now applies to the actual parent
and child graph ratios. Recursion, real input bounds, absent-child values and
actual pruning are derived, not supplied as message-semantics hypotheses. -/
theorem actual_grid_affine_contraction (V : Finset Point) (i : Fin 881)
    (h0 : (0, 0) ∈ V) (hdis : Disjoint V (radiusFourMask i))
    («λ» : ℝ) («hλ» : 0 ≤ «λ» ∧ «λ» ≤ 51 / 20) :
    (1 - gridVacancy V (0, 0) «λ») *
        (∑ d ∈ availableDirections V,
          childMessage i d (childVacancy V (radiusFourChoice i) d «λ»)) /
      affineMessage i (gridVacancy V (0, 0) «λ») < 999 / 1000 := by
  let x : Fin 3 → ℝ := fun d => childVacancy V (radiusFourChoice i) d «λ»
  have hx (d) : (20 / 71 : ℝ) ≤ x d ∧ x d ≤ 1 :=
    real_255_message_box squareGrid (advance V (radiusFourChoice i) d) (0, 0) «λ» «hλ»
  have hp : (-1, 0) ∉ V := by
    intro hv
    exact (Finset.disjoint_left.mp hdis) hv (radiusFour_geometry.2.2.2.1 i).2.2.1
  have hmask : (fun d => if d ∈ availableDirections V then x d else 1) = x := by
    funext d
    by_cases hd : direction d ∈ V
    · simp [availableDirections, hd]
    · have hv := child_vacancy_absent V (radiusFourChoice i) d hd «λ» «hλ».1
      simp [availableDirections, hd, x, hv]
  have hy : vacancy «λ» (fun d => if d ∈ availableDirections V then x d else 1) =
      gridVacancy V (0, 0) «λ» := by
    rw [hmask, grid_real_recursion V h0 hp (radiusFourChoice i) «λ» «hλ».1]
    simp only [vacancy, x, one_div]
  have h := affine_pruned_row_contraction i (availableDirections V) «λ» «hλ» x hx
  dsimp only at h
  rw [hy] at h
  exact h

#print axioms child_vacancy_before
#print axioms ordered_product_children
#print axioms grid_vacancy_product_telescopes
#print axioms grid_partition_recursion
#print axioms grid_real_recursion
#print axioms child_vacancy_absent
#print axioms typed_child_context
#print axioms actual_grid_affine_contraction

end D5.S3.StatisticalMechanics.HardCore.SquareGridMessages
