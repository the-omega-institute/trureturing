/- GID: D5/S3/Quantum/Tomography/MUBModeAffinityEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBModeAffinityEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Under the rowwise collision threshold, context affinity one forces every row onto the exact collision-equality locus. -/

import D5.S3.Quantum.Tomography.MUBModeCharacterEnergy

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBModeAffinityEquality

open D5.S3.Quantum.Tomography.MUBModeSymmetryBudget
open D5.S3.Quantum.Tomography.MUBModeAffinitySharpBound
open D5.S3.Quantum.Tomography.MUBModeCharacterEnergy

/-- If all six row collisions are at least `2 / 3` and total affinity is one,
then every row collision equals `2 / 3`. -/
theorem row_collision_eq_two_thirds_of_affinity_eq_one
    (p : Fin 6 → Fin 3 → ℝ)
    (hrow : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (p i))
    (haff : modeAffinityTotal p = 1) :
    ∀ i, threeModeCollision (p i) = (2 / 3 : ℝ) := by
  have hcollision : modeCollisionTotal p = 4 := by
    unfold modeAffinityTotal at haff
    linarith
  have hsum :
      ∑ i, (threeModeCollision (p i) - (2 / 3 : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change modeCollisionTotal p - ∑ _i : Fin 6, (2 / 3 : ℝ) = 0
    rw [hcollision]
    norm_num
  have hzero :
      ∀ i, threeModeCollision (p i) - (2 / 3 : ℝ) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi ↦ sub_nonneg.mpr (hrow i))).mp hsum
  intro i
  linarith [hzero i]

/-- On normalized rows, affinity equality places every row on character square
`1 / 2`. -/
theorem row_characterSquare_eq_half_of_affinity_eq_one
    (p : Fin 6 → Fin 3 → ℝ)
    (hsum : ∀ i, p i 0 + p i 1 + p i 2 = 1)
    (hrow : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (p i))
    (haff : modeAffinityTotal p = 1) :
    ∀ i, threeModeCharacterSquare (p i) = (1 / 2 : ℝ) := by
  intro i
  rw [threeModeCharacterSquare_eq_of_sum_one (p i) (hsum i)]
  rw [row_collision_eq_two_thirds_of_affinity_eq_one p hrow haff i]
  norm_num

/-- For a pair obeying the MUB budget and the rowwise collision threshold on
both sides, every one of the twelve rows lies on the exact equality level. -/
theorem completion_pair_rows_forced_to_collision_equality
    (p q : Fin 6 → Fin 3 → ℝ)
    (hp : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (p i))
    (hq : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (q i))
    (hbudget : modeAffinityTotal p + modeAffinityTotal q ≤ 2) :
    (∀ i, threeModeCollision (p i) = (2 / 3 : ℝ)) ∧
      (∀ i, threeModeCollision (q i) = (2 / 3 : ℝ)) := by
  obtain ⟨hpAffinity, hqAffinity⟩ :=
    completion_pair_forced_to_affinity_one p q hp hq hbudget
  exact ⟨
    row_collision_eq_two_thirds_of_affinity_eq_one p hp hpAffinity,
    row_collision_eq_two_thirds_of_affinity_eq_one q hq hqAffinity
  ⟩

#print axioms row_collision_eq_two_thirds_of_affinity_eq_one
#print axioms row_characterSquare_eq_half_of_affinity_eq_one
#print axioms completion_pair_rows_forced_to_collision_equality

end D5.S3.Quantum.Tomography.MUBModeAffinityEquality
