/- GID: D5/S1/Recurrence/RotationOrbitGapsPartition
   generality: G
   mirror-B: D5/B/S1/Recurrence/RotationOrbitGapsPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fractional rotation orbits have positive gaps partitioning the circle. -/

import D5.S1.Recurrence.CyclicGapsPartition
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum

namespace D5.S1.Recurrence.RotationOrbitGapsPartition

open D5.S1.Recurrence.CyclicGapsPartition
open D5.S1.Recurrence.CyclicNearestReturn

/-- The first `n` points of rotation by `α`, represented in the half-open unit interval. -/
noncomputable def rotationOrbit (α : ℝ) (n : ℕ) : Finset ℝ :=
  (Finset.range n).image fun (k : ℕ) => Int.fract ((k : ℝ) * α)

/-- A positive-length rotation orbit contains its zeroth point. -/
noncomputable def rotationOrbitNonempty (α : ℝ) (n : ℕ) (hn : 0 < n) :
    (rotationOrbit α n).Nonempty := by
  rw [rotationOrbit, Finset.image_nonempty]
  exact ⟨0, Finset.mem_range.mpr hn⟩

/-- A nonempty finite rotation orbit has positive clockwise gaps summing to one. -/
theorem rotation_orbit_gaps_partition (α : ℝ) (n : ℕ) :
    (↑(rotationOrbit α n) : Set ℝ) ⊆ Set.Ico 0 1 ∧
    (0 < n → (rotationOrbit α n).Nonempty) ∧
    (∀ hn : 0 < n,
      (∀ x ∈ rotationOrbit α n,
        0 < gap (rotationOrbit α n) (rotationOrbitNonempty α n hn) x) ∧
      ∑ x ∈ rotationOrbit α n,
        gap (rotationOrbit α n) (rotationOrbitNonempty α n hn) x = 1) := by
  have hUnit : (↑(rotationOrbit α n) : Set ℝ) ⊆ Set.Ico 0 1 := by
    intro x hx
    change x ∈ rotationOrbit α n at hx
    rw [rotationOrbit, Finset.mem_image] at hx
    rcases hx with ⟨k, hk, rfl⟩
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hNonempty := rotationOrbitNonempty α n
  refine ⟨hUnit, hNonempty, ?_⟩
  intro hn
  have hOrbit := rotationOrbitNonempty α n hn
  rcases cyclic_gaps_partition_circle (rotationOrbit α n) hUnit hOrbit with
    ⟨_, hPositive, hSum⟩
  exact ⟨hPositive, hSum⟩

-- This two-point orbit uses the ordinary successor at zero and the wrap at one half.
example :
    let S := rotationOrbit (1 / 2 : ℝ) 2
    let hS : S.Nonempty := rotationOrbitNonempty (1 / 2 : ℝ) 2 (by norm_num)
    S = {0, 1 / 2} ∧ cyclicSucc S hS 0 = 1 / 2 ∧
      0 ≠ S.max' hS ∧ 1 / 2 = S.max' hS ∧
      ∑ x ∈ S, gap S hS x = 1 := by
  dsimp only
  have hFractInv : Int.fract (2⁻¹ : ℝ) = 2⁻¹ := by
    exact Int.fract_eq_self.mpr ⟨by positivity, by norm_num⟩
  have hOrbit : rotationOrbit (1 / 2 : ℝ) 2 = {0, 1 / 2} := by
    rw [rotationOrbit, show Finset.range 2 = {0, 1} by decide]
    simp [hFractInv]
  have hSucc :
      cyclicSucc (rotationOrbit (1 / 2 : ℝ) 2)
        (rotationOrbitNonempty (1 / 2 : ℝ) 2 (by norm_num)) 0 = 1 / 2 := by
    have hFilter :
        (rotationOrbit (1 / 2 : ℝ) 2).filter (fun y => (0 : ℝ) < y) = {1 / 2} := by
      ext y
      rw [Finset.mem_filter, hOrbit]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hPositive⟩
        · norm_num at hPositive
        · rfl
      · rintro rfl
        norm_num
    have hAbove :
        ((rotationOrbit (1 / 2 : ℝ) 2).filter (fun y => (0 : ℝ) < y)).Nonempty := by
      rw [hFilter]
      exact ⟨1 / 2, Finset.mem_singleton_self _⟩
    rw [cyclicSucc, dif_pos hAbove]
    apply le_antisymm
    · apply Finset.min'_le
      rw [hFilter]
      exact Finset.mem_singleton_self _
    · apply Finset.le_min'
      intro y hy
      rw [hFilter] at hy
      exact le_of_eq (Finset.mem_singleton.mp hy).symm
  have hMax :
      (rotationOrbit (1 / 2 : ℝ) 2).max'
        (rotationOrbitNonempty (1 / 2 : ℝ) 2 (by norm_num)) = 1 / 2 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      rw [hOrbit] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> norm_num
    · apply Finset.le_max'
      rw [hOrbit]
      simp
  have hSum :=
    (rotation_orbit_gaps_partition (1 / 2 : ℝ) 2).2.2 (by norm_num)
  exact ⟨hOrbit, hSucc, by rw [hMax]; norm_num, hMax.symm, hSum.2⟩

end D5.S1.Recurrence.RotationOrbitGapsPartition
