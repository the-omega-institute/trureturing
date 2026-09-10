/- GID: D5/S3/HardCoreHolomorphic/NormalizedPartitionLog
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/NormalizedPartitionLog
   mirror-E: none(waiver:exact-branch-correct-finite-volume-logarithm)
   anchors: []
   digest: Complete deletion orders define one normalized holomorphic logarithm of the actual grid partition. -/

import D5.S3.HardCoreHolomorphic.PartitionLogCocycle

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.NormalizedPartitionLog

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood
open D5.S3.HardCoreHolomorphic.FiniteGridZeroFree
open D5.S3.HardCoreHolomorphic.PartitionLogCocycle

/-- Sum principal logs of the actual successive deletion ratios. The list may
be partial or contain repeated/absent vertices; those cases are not silently discarded. -/
def orderedLog (V : Finset Point) : List Point → ℂ → ℂ
  | [], _ => 0
  | v :: l, z => Complex.log (increment V v z) + orderedLog (V.erase v) l z

/-- Local square flatness proves exact order independence by adjacent swaps.
This does not identify the total sum with the principal logarithm of the full partition. -/
theorem ordered_log_perm {l₁ l₂ : List Point} (h : l₁.Perm l₂)
    (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    orderedLog V l₁ z = orderedLog V l₂ z := by
  induction h generalizing V with
  | nil => rfl
  | cons v h ih =>
      simp only [orderedLog]
      rw [ih (V.erase v)]
  | swap u v l =>
      have he : (V.erase u).erase v = (V.erase v).erase u := by
        ext p
        simp only [Finset.mem_erase]
        tauto
      simp only [orderedLog, ← add_assoc]
      rw [increment_log_square V v u z hz, he]
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ V).trans (ih₂ V)

/-- Exponentiation telescopes to the exact quotient for an arbitrary deletion
list. Nonzero denominators are derived from the established common grid tube. -/
theorem ordered_log_exp (V : Finset Point) (l : List Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    Complex.exp (orderedLog V l z) = gridPartition V z / gridPartition (afterErases V l) z := by
  induction l generalizing V with
  | nil => simp [orderedLog, afterErases, finite_grid_zero_free V z hz]
  | cons v l ih =>
      rw [orderedLog, Complex.exp_add,
        Complex.exp_log (increment_ne_zero V v z hz), ih]
      simp only [increment, afterErases]
      field_simp [finite_grid_zero_free (V.erase v) z hz,
        finite_grid_zero_free (afterErases (V.erase v) l) z hz] <;> ring

/-- Ordered logs are normalized to zero at zero activity, without a branch choice
based on a floating approximation. -/
theorem ordered_log_zero (V : Finset Point) (l : List Point) : orderedLog V l 0 = 0 := by
  induction l generalizing V with
  | nil => rfl
  | cons v l ih => simp [orderedLog, increment, grid_partition_zero, ih]

/-- The complete differential telescopes just like the partition products.
This theorem covers arbitrary partial lists and all complex points in the tube. -/
theorem ordered_log_hasDerivAt (V : Finset Point) (l : List Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    HasDerivAt (orderedLog V l)
      (response V z - response (afterErases V l) z) z := by
  induction l generalizing V with
  | nil => simpa [orderedLog, afterErases] using hasDerivAt_const z (0 : ℂ)
  | cons v l ih =>
      have h := (increment_log_hasDerivAt V v z hz).add (ih (V.erase v))
      convert! h using 1
      simp only [afterErases]
      ring

/-- A canonical value chosen using the finite set's existing list enumeration.
Its agreement with every complete distinct enumeration is proved below. -/
def normalizedLog (V : Finset Point) (z : ℂ) : ℂ := orderedLog V V.toList z

/-- Every complete, repetition-free deletion list gives the same normalized
value. Thus the choice of Finset.toList is not mathematical data of the result. -/
theorem complete_order_eq (V : Finset Point) (l : List Point)
    (hl : l.Nodup) (hV : l.toFinset = V) (z : ℂ) (hz : z ∈ ActivityTube) :
    orderedLog V l z = normalizedLog V z := by
  have hp : l.Perm V.toList := by
    apply (List.perm_ext_iff_of_nodup hl V.nodup_toList).mpr
    intro v
    have h : v ∈ l.toFinset ↔ v ∈ V := by rw [hV]
    simpa using h
  exact ordered_log_perm hp V z hz

private theorem complete_erases (V : Finset Point) : afterErases V V.toList = ∅ := by
  simp [afterErases_eq_sdiff]

/-- The normalized logarithm exponentiates to the actual independent-set sum. -/
theorem normalized_log_exp (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    Complex.exp (normalizedLog V z) = gridPartition V z := by
  have h := ordered_log_exp V V.toList z hz
  simpa only [normalizedLog, complete_erases, gridPartition, partition_empty, div_one] using h

/-- Canonical normalization at the activity-zero endpoint. -/
theorem normalized_log_zero (V : Finset Point) : normalizedLog V 0 = 0 :=
  ordered_log_zero V V.toList

/-- The normalized branch has precisely the actual logarithmic derivative Z'/Z. -/
theorem normalized_log_hasDerivAt (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    HasDerivAt (normalizedLog V) (response V z) z := by
  change HasDerivAt (orderedLog V V.toList) (response V z) z
  have h := ordered_log_hasDerivAt V V.toList z hz
  have he : response ∅ z = 0 := by simp [response, gridPartition, partition_empty]
  simpa only [complete_erases, he, sub_zero] using h

/-- Holomorphy on the original common activity neighborhood, with no new width
or graph-dependent analytic-continuation premise. -/
theorem normalized_log_differentiableOn (V : Finset Point) :
    DifferentiableOn ℂ (normalizedLog V) ActivityTube := by
  intro z hz
  exact (normalized_log_hasDerivAt V z hz).differentiableAt.differentiableWithinAt

/-- The actual real part equals log of the actual partition modulus. Only the
real part, not the full complex value, is identified with the principal log. -/
theorem normalized_log_re (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    (normalizedLog V z).re = Real.log ‖gridPartition V z‖ := by
  have h := congrArg norm (normalized_log_exp V z hz)
  rw [Complex.norm_exp] at h
  calc
    _ = Real.log (Real.exp (normalizedLog V z).re) := (Real.log_exp _).symm
    _ = _ := congrArg Real.log h

private theorem ordered_im_bound (V : Finset Point) (l : List Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    |(orderedLog V l z).im| ≤ (l.length : ℝ) * (Real.pi / 2) := by
  induction l generalizing V with
  | nil => simp [orderedLog]
  | cons v l ih =>
      simp only [orderedLog, Complex.add_im, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ |(Complex.log (increment V v z)).im| + |(orderedLog (V.erase v) l z).im| := abs_add_le _ _
        _ ≤ Real.pi / 2 + (l.length : ℝ) * (Real.pi / 2) :=
          add_le_add (increment_log_im V v z hz).le (ih (V.erase v))
        _ = _ := by ring

/-- A volume-linear imaginary bound for the chosen analytic branch. This allows
winding of the total partition while controlling it uniformly per vertex. -/
theorem normalized_log_im_bound (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    |(normalizedLog V z).im| ≤ (V.card : ℝ) * (Real.pi / 2) := by
  simpa [normalizedLog] using ordered_im_bound V V.toList z hz

/-- Exact canonical deletion recursion. The complete logarithm may accumulate
phase, yet its one-vertex increment is always the local principal logarithm. -/
theorem normalized_log_delete (V : Finset Point) (v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    normalizedLog V z = Complex.log (increment V v z) + normalizedLog (V.erase v) z := by
  by_cases hv : v ∈ V
  · have hnodup : (v :: (V.erase v).toList).Nodup := by
      exact List.nodup_cons.mpr ⟨by simp, (V.erase v).nodup_toList⟩
    have hset : (v :: (V.erase v).toList).toFinset = V := by
      simp [Finset.insert_erase hv]
    have h := complete_order_eq V (v :: (V.erase v).toList) hnodup hset z hz
    exact h.symm
  · simp [increment, Finset.erase_eq_of_notMem hv, finite_grid_zero_free V z hz]

/-- The normalized finite-volume logarithm is bounded linearly in volume,
with constants independent of the domain, its boundary and the deletion order. -/
theorem normalized_log_volume_bounds (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    -(V.card : ℝ) * Real.log 2 ≤ (normalizedLog V z).re ∧
    (normalizedLog V z).re ≤ (V.card : ℝ) * Real.log 4 ∧
    |(normalizedLog V z).im| ≤ (V.card : ℝ) * (Real.pi / 2) := by
  have hlo := finite_grid_partition_lower V z hz
  have hn : 0 < ‖gridPartition V z‖ := norm_pos_iff.mpr (finite_grid_zero_free V z hz)
  have hz3 : ‖z‖ < 3 := by
    obtain ⟨lam, hlam, he⟩ := hz
    have ht := norm_le_norm_sub_add z (lam : ℂ)
    have hl : ‖(lam : ℂ)‖ = lam := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam.1]
    rw [hl] at ht
    have hw : D5.S3.HardCoreHolomorphic.TubeEstimates.epsilon < (1 / 4 : ℝ) := by
      norm_num [D5.S3.HardCoreHolomorphic.TubeEstimates.epsilon]
    linarith [hlam.2]
  have hup : ‖gridPartition V z‖ ≤ (4 : ℝ) ^ V.card := by
    calc
      _ ≤ (1 + ‖z‖) ^ V.card := grid_partition_norm_upper V z
      _ ≤ _ := by gcongr; linarith
  have hlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) V.card) hlo
  have hupp := Real.log_le_log hn hup
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [Real.log_pow, hhalf] at hlow
  rw [Real.log_pow] at hupp
  exact ⟨by rw [normalized_log_re V z hz]; nlinarith,
    by rwa [normalized_log_re V z hz], normalized_log_im_bound V z hz⟩

#print axioms normalized_log_volume_bounds
#print axioms ordered_log_perm
#print axioms ordered_log_exp
#print axioms ordered_log_zero
#print axioms ordered_log_hasDerivAt
#print axioms complete_order_eq
#print axioms normalized_log_exp
#print axioms normalized_log_zero
#print axioms normalized_log_hasDerivAt
#print axioms normalized_log_differentiableOn
#print axioms normalized_log_re
#print axioms normalized_log_im_bound
#print axioms normalized_log_delete

end D5.S3.HardCoreHolomorphic.NormalizedPartitionLog
