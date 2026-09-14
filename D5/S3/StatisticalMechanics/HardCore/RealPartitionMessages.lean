/- GID: D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/RealPartitionMessages
   mirror-E: none(waiver:actual-partition-message-identification)
   anchors: []
   utility: none
   digest: Actual finite-graph vacancy ratios satisfy the recursion and certified real box. -/

import D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.RealPartitionMessages

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion

variable {α : Type*} [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Nonnegative activities make the actual partition monotone in its domain. -/
theorem partition_mono (w : α → ℝ) (U V : Finset α) (hUV : U ⊆ V)
    (hw : ∀ v ∈ V, 0 ≤ w v) : partition G U w ≤ partition G V w := by
  have hc : configurations G U ⊆ configurations G V := by
    intro S hS
    simp only [configurations, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨hS.1.trans hUV, hS.2⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg hc
  intro S hS _
  have hsub : S ⊆ V := (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  apply Finset.prod_nonneg
  intro v hv
  exact hw v (hsub hv)

/-- The real vacancy message is the ratio of two actual independent-set sums. -/
noncomputable def vacancyRatio (V : Finset α) (v : α) (w : α → ℝ) : ℝ :=
  partition G (V.erase v) w / partition G V w

/-- The invariant real box follows from actual graph partitions, with no
supplied positivity or message-interpretation premise. It also covers an
absent root, whose vacancy ratio is one. -/
theorem vacancy_bounds (w : α → ℝ) (V : Finset α) (v : α) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hw : ∀ u ∈ V, 0 ≤ w u) (hvΛ : w v ≤ Λ) :
    1 / (1 + Λ) ≤ vacancyRatio G V v w ∧ vacancyRatio G V v w ≤ 1 := by
  have hZ := one_le_partition G V w hw
  have hZpos : 0 < partition G V w := lt_of_lt_of_le zero_lt_one hZ
  have hΛpos : 0 < 1 + Λ := by linarith
  by_cases hv : v ∈ V
  · have hw0 : ∀ u ∈ V.erase v, 0 ≤ w u :=
      fun u hu => hw u (Finset.mem_of_mem_erase hu)
    have hZ0 := one_le_partition G (V.erase v) w hw0
    have hm := partition_mono G w (V.erase v) V (Finset.erase_subset _ _) hw
    have hC : partition G (closedComplement G V v) w ≤ partition G (V.erase v) w :=
      partition_mono G w _ _ (Finset.filter_subset _ _) hw0
    have hmul := mul_le_mul_of_nonneg_left hC (hw v hv)
    have hroot := mul_le_mul_of_nonneg_right hvΛ
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hZ0)
    have hupper : partition G V w ≤ (1 + Λ) * partition G (V.erase v) w := by
      rw [partition_delete G V v hv w]
      nlinarith
    constructor
    · apply (div_le_div_iff₀ hΛpos hZpos).mpr
      nlinarith
    · apply (div_le_iff₀ hZpos).mpr
      simpa using hm
  · rw [vacancyRatio, Finset.erase_eq_of_notMem hv, div_self (ne_of_gt hZpos)]
    exact ⟨(div_le_iff₀ hΛpos).mpr (by linarith), le_rfl⟩

/-- The reciprocal hard-core recursion is derived for the actual vacancy
ratio. All intermediate nonzero facts follow from nonnegative activities. -/
theorem real_ordered_vacancy (w : α → ℝ) (V : Finset α) (v : α)
    (hv : v ∈ V) (l : List α) (hl : l.toFinset = V.filter (G.Adj v))
    (hw : ∀ u ∈ V, 0 ≤ w u) :
    vacancyRatio G V v w = (1 + w v * vacancyProduct G w (V.erase v) l)⁻¹ := by
  have hproper (U : Finset α) (hU : U ⊆ V.erase v) : partition G U w ≠ 0 := by
    have h := one_le_partition G U w (fun u hu => hw u (Finset.mem_of_mem_erase (hU hu)))
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one h)
  have hp := partition_ordered_recursion G w V v hv l hl hproper
  have hZne : partition G V w ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_partition G V w hw))
  have hZ0ne := hproper (V.erase v) (by intro u hu; exact hu)
  have hDne : 1 + w v * vacancyProduct G w (V.erase v) l ≠ 0 := by
    intro hD
    have hz : partition G V w = 0 := by simpa [hD] using hp
    exact hZne hz
  rw [vacancyRatio, hp]
  field_simp [hZ0ne, hDne]

/-- Every actual finite-graph message at activities in [0,2.55] belongs to
exactly the box used by the 881-state affine-message certificate. -/
theorem real_255_message_box (V : Finset α) (v : α) («λ» : ℝ)
    («hλ» : 0 ≤ «λ» ∧ «λ» ≤ 51 / 20) :
    vacancyRatio G V v (fun _ => «λ») ∈ Set.Icc (20 / 71) 1 := by
  have h := vacancy_bounds G (fun _ => «λ») V v (51 / 20)
    (by norm_num) (fun _ _ => «hλ».1) «hλ».2
  norm_num at h
  exact h

#print axioms partition_mono
#print axioms vacancy_bounds
#print axioms real_ordered_vacancy
#print axioms real_255_message_box

end D5.S3.StatisticalMechanics.HardCore.RealPartitionMessages
