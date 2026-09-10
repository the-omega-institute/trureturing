/- GID: D5/S3/HardCoreHolomorphic/ActualGraphLift
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/ActualGraphLift
   mirror-E: none(waiver:exact-complex-graph-message-lift)
   anchors: []
   digest: Lift actual proper-domain ratios into the existing complex message neighborhoods. -/

import D5.S3.StatisticalMechanics.HardCore.SquareGridRootMessages
import D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.ActualGraphLift

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.StatisticalMechanics.HardCore.SquareGridMessages
open D5.S3.StatisticalMechanics.HardCore.SquareGridRootMessages
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates
open D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessageData
open D5.S3.HardCoreHolomorphic.AffineChart
open D5.S3.HardCoreHolomorphic.TypedJacobian
open D5.S3.HardCoreHolomorphic.TubeEstimates
open D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood

/-- Specialize the existing analytic inverse to the actual coefficient owner.
This exposes its value without naming the analytic module's private accessors. -/
abbrev decode (i : Fin 881) (m : ℂ) : ℂ :=
  inverse (((affineCoefficients i).1 : ℝ) : ℂ)
    (((affineCoefficients i).2 : ℝ) : ℂ) m

/-- The exact coordinate of a missing child, whose vacancy is one. -/
def neutralMessage (i : Fin 881) : ℂ :=
  center ((affineCoefficients i).1 : ℝ) ((affineCoefficients i).2 : ℝ) 1

/-- Every type has a genuine neutral message inside its open neighborhood. -/
theorem neutral_message (i : Fin 881) :
    neutralMessage i ∈ Omega i ∧ decode i (neutralMessage i) = 1 := by
  have hc := actual_coefficient_bounds i
  change 0 ≤ ((affineCoefficients i).1 : ℝ) ∧
    (1 / 100 : ℝ) ≤ ((affineCoefficients i).2 : ℝ) - (affineCoefficients i).1 ∧
    ((affineCoefficients i).2 : ℝ) ≤ 3 at hc
  constructor
  · refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
    change ‖neutralMessage i - neutralMessage i‖ < delta
    simpa using width_arithmetic.1
  · exact inverse_center _ _ 1 (by linarith [hc.1, hc.2.1])
      (by norm_num) (by simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 100) hc.2.1)

/-- A missing nonroot direction has complex vacancy one once only the
proper pre-recentered partitions are known nonzero. Real positivity is not used. -/
theorem complex_child_absent (V : Finset Point) (a : Fin 6) (d : Fin 3)
    (z : ℂ) (hd : direction d ∉ V)
    (hproper : ∀ U : Finset Point, U ⊆ V.erase (0, 0) → gridPartition U z ≠ 0) :
    childVacancy V a d z = 1 := by
  rw [child_vacancy_before]
  have hn := hproper (V \ deleted a d) (before_child_subset_erase V a d)
  have hnot : direction d ∉ V \ deleted a d :=
    fun h => hd (Finset.mem_sdiff.mp h).1
  simp only [gridVacancy, Finset.erase_eq_of_notMem hnot, div_self hn]

/-- The missing fourth-root factors also have value one using only smaller
pre-recentered domains. No nonzero root partition is assumed. -/
theorem complex_root_child_absent (V : Finset Point) (e : Fin 4)
    (z : ℂ) (he : rootDirection e ∉ V)
    (hproper : ∀ U : Finset Point, U ⊆ V.erase (0, 0) → gridPartition U z ≠ 0) :
    gridVacancy (rootDomain V e) (0, 0) z = 1 := by
  rw [root_child_vacancy]
  have hsub : afterErases (V.erase (0, 0)) (rootEarlier e) ⊆ V.erase (0, 0) := by
    rw [afterErases_eq_sdiff]
    exact Finset.sdiff_subset
  have hnot : rootDirection e ∉ afterErases (V.erase (0, 0)) (rootEarlier e) :=
    fun h => he (Finset.mem_of_mem_erase (hsub h))
  simp only [gridVacancy, Finset.erase_eq_of_notMem hnot, div_self (hproper _ hsub)]

/-- The actual vertex-membership pruning is legal in the existing finite
geometric presentation. Its successor type and smaller domain are derived. -/
theorem actual_pruning (V : Finset Point) (i : Fin 881)
    (h0 : (0, 0) ∈ V) (hdis : Disjoint V (radiusFourMask i)) :
    Pruning i (availableDirections V) := by
  intro d hd
  have hv : direction d ∈ V := (Finset.mem_filter.mp hd).2
  obtain ⟨j, hj, _⟩ := typed_child_context V i h0 hdis d hv
  exact ⟨j, hj⟩

/-- Algebraically identify the represented child product with the complete
actual graph product, inserting only the rigorously proved neutral factors. -/
theorem decoded_child_product (V : Finset Point) (i : Fin 881) (z : ℂ)
    (hproper : ∀ U : Finset Point, U ⊆ V.erase (0, 0) → gridPartition U z ≠ 0)
    (m : Fin 3 → ℂ)
    (hm : ∀ d ∈ availableDirections V,
      decode (childType i d) (m d) = childVacancy V (radiusFourChoice i) d z) :
    (∏ d ∈ availableDirections V, decode (childType i d) (m d)) =
      ∏ d, childVacancy V (radiusFourChoice i) d z := by
  symm
  calc
    _ = ∏ d : Fin 3, if d ∈ availableDirections V then
          decode (childType i d) (m d) else 1 := by
      apply Finset.prod_congr rfl
      intro d _
      by_cases hd : d ∈ availableDirections V
      · rw [if_pos hd]
        exact (hm d hd).symm
      · rw [if_neg hd]
        apply complex_child_absent V (radiusFourChoice i) d z _ hproper
        simpa only [availableDirections, Finset.mem_filter, Finset.mem_univ,
          true_and] using hd
    _ = _ := by simp

/-- One genuine internal graph step consumes smaller-domain nonvanishing and
actual child representations. It derives the parent nonvanishing and its
message representation, without assuming either parent conclusion. -/
theorem typed_graph_step (V : Finset Point) (i : Fin 881)
    (h0 : (0, 0) ∈ V) (hdis : Disjoint V (radiusFourMask i))
    (z : ℂ) (hz : z ∈ ActivityTube)
    (hproper : ∀ U : Finset Point, U ⊆ V.erase (0, 0) → gridPartition U z ≠ 0)
    (hchildren : ∀ d ∈ availableDirections V, ∃ m : ℂ,
      m ∈ Omega (childType i d) ∧
      decode (childType i d) m = childVacancy V (radiusFourChoice i) d z) :
    gridPartition V z ≠ 0 ∧
      ∃ m : ℂ, m ∈ Omega i ∧ decode i m = gridVacancy V (0, 0) z := by
  have hex : ∀ d : Fin 3, ∃ m : ℂ, m ∈ Omega (childType i d) ∧
      (d ∈ availableDirections V →
        decode (childType i d) m = childVacancy V (radiusFourChoice i) d z) := by
    intro d
    by_cases hd : d ∈ availableDirections V
    · obtain ⟨m, hm, he⟩ := hchildren d hd
      exact ⟨m, hm, fun _ => he⟩
    · exact ⟨neutralMessage (childType i d), (neutral_message _).1,
        fun h => False.elim (hd h)⟩
  choose m hm he using hex
  have hs := actual_pruning V i h0 hdis
  have hi := adaptive_uniform_invariant i (availableDirections V) hs z hz m (fun d _ => hm d)
  have hr := (adaptive_holomorphic_recovery i (availableDirections V) hs z hz m
    (fun d _ => hm d)).2
  let P : ℂ := ∏ d ∈ availableDirections V, decode (childType i d) (m d)
  have hp := decoded_child_product V i z hproper m he
  have hDre : (1 / 2 : ℝ) ≤ (1 + z * P).re := hi.2.2.1
  have hD : 1 + z * P ≠ 0 := by
    intro h
    norm_num [h] at hDre
  have hparent : (-1, 0) ∉ V := by
    intro hv
    exact (Finset.disjoint_left.mp hdis) hv (radiusFour_geometry.2.2.2.1 i).2.2.1
  have hrec : gridPartition V z = gridPartition (V.erase (0, 0)) z * (1 + z * P) := by
    simpa only [← hp] using grid_partition_recursion V h0 hparent (radiusFourChoice i) z hproper
  have hsmall := hproper (V.erase (0, 0)) (by intro p hp; exact hp)
  have hn : gridPartition V z ≠ 0 := by
    rw [hrec]
    exact mul_ne_zero hsmall hD
  refine ⟨hn, adaptiveMap i (availableDirections V) z m, hi.1, ?_⟩
  change decode i (adaptiveMap i (availableDirections V) z m) = (1 + z * P)⁻¹ at hr
  rw [hr]
  unfold gridVacancy
  rw [hrec]
  field_simp [hsmall, hD]

/-- Reconstruct the unconditioned root from actual type-zero child messages.
The half-plane bound is retained for a quantitative partition lower bound. -/
theorem root_graph_step (V : Finset Point) (h0 : (0, 0) ∈ V)
    (z : ℂ) (hz : z ∈ ActivityTube)
    (hproper : ∀ U : Finset Point, U ⊆ V.erase (0, 0) → gridPartition U z ≠ 0)
    (hchildren : ∀ e : Fin 4, rootDirection e ∈ V → ∃ m : ℂ,
      m ∈ Omega 0 ∧ decode 0 m = gridVacancy (rootDomain V e) (0, 0) z) :
    ∃ D : ℂ, (1 / 2 : ℝ) ≤ D.re ∧
      gridPartition V z = gridPartition (V.erase (0, 0)) z * D := by
  have hex : ∀ e : Fin 4, ∃ m : ℂ, m ∈ Omega 0 ∧
      decode 0 m = gridVacancy (rootDomain V e) (0, 0) z := by
    intro e
    by_cases he : rootDirection e ∈ V
    · exact hchildren e he
    · refine ⟨neutralMessage 0, (neutral_message 0).1, ?_⟩
      rw [(neutral_message 0).2, complex_root_child_absent V e z he hproper]
  choose m hm he using hex
  have hD := (four_child_root_nonzero z hz m hm).1
  have hp : (∏ e : Fin 4, decode 0 (m e)) =
      ∏ e : Fin 4, gridVacancy (rootDomain V e) (0, 0) z := by
    exact Finset.prod_congr rfl (fun e _ => he e)
  refine ⟨1 + z * ∏ e : Fin 4, decode 0 (m e), hD, ?_⟩
  rw [hp]
  exact root_partition_recursion V h0 z hproper

#print axioms neutral_message
#print axioms complex_child_absent
#print axioms complex_root_child_absent
#print axioms actual_pruning
#print axioms decoded_child_product
#print axioms typed_graph_step
#print axioms root_graph_step

end D5.S3.HardCoreHolomorphic.ActualGraphLift
