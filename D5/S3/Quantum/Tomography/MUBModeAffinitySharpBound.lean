/- GID: D5/S3/Quantum/Tomography/MUBModeAffinitySharpBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBModeAffinitySharpBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A rowwise three-mode collision threshold accumulates to a context affinity threshold; the MUB budget then isolates or excludes double completions. -/

import D5.S3.Quantum.Tomography.MUBModeSymmetryBudget

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBModeAffinitySharpBound

open D5.S3.Quantum.Tomography.MUBModeSymmetryBudget

/-- If every row has three-mode collision at least `2 / 3`, the six-row
symmetry-affinity coordinate is at least one. -/
theorem one_le_modeAffinityTotal_of_row_collision
    (p : Fin 6 → Fin 3 → ℝ)
    (hrow : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (p i)) :
    1 ≤ modeAffinityTotal p := by
  have htotal : (4 : ℝ) ≤ modeCollisionTotal p := by
    unfold modeCollisionTotal
    calc
      (4 : ℝ) = ∑ _i : Fin 6, (2 / 3 : ℝ) := by norm_num
      _ ≤ ∑ i, threeModeCollision (p i) :=
        Finset.sum_le_sum fun i hi ↦ hrow i
  unfold modeAffinityTotal
  linarith

/-- The same rowwise collision threshold bounds total mode mixing by two. -/
theorem modeMixingTotal_le_two_of_row_collision
    (p : Fin 6 → Fin 3 → ℝ)
    (hrow : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (p i)) :
    modeMixingTotal p ≤ 2 := by
  rw [modeMixingTotal_eq_four_sub_two_mul_affinity]
  linarith [one_le_modeAffinityTotal_of_row_collision p hrow]

/-- Two quantities that each exceed one cannot satisfy the two-dimensional
symmetry-plane budget. -/
theorem no_affinity_pair_above_one
    (a b : ℝ)
    (ha : 1 < a) (hb : 1 < b)
    (hbudget : a + b ≤ 2) : False := by
  linarith

/-- If both members of a pair obey the lower threshold one and jointly obey the
budget two, then both lie exactly on the equality locus. -/
theorem affinity_pair_eq_one_of_lower_bounds_and_budget
    (a b : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbudget : a + b ≤ 2) :
    a = 1 ∧ b = 1 := by
  constructor <;> linarith

/-- A rowwise `2 / 3` collision bound for each of two completions, together
with the MUB symmetry budget, forces equality of both context affinities. This
is the exact reduction from a weak branch bound to an equality-locus problem. -/
theorem completion_pair_forced_to_affinity_one
    (p q : Fin 6 → Fin 3 → ℝ)
    (hp : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (p i))
    (hq : ∀ i, (2 / 3 : ℝ) ≤ threeModeCollision (q i))
    (hbudget : modeAffinityTotal p + modeAffinityTotal q ≤ 2) :
    modeAffinityTotal p = 1 ∧ modeAffinityTotal q = 1 := by
  exact affinity_pair_eq_one_of_lower_bounds_and_budget
    (modeAffinityTotal p) (modeAffinityTotal q)
    (one_le_modeAffinityTotal_of_row_collision p hp)
    (one_le_modeAffinityTotal_of_row_collision q hq)
    hbudget

/-- Any strict context-level lower bound above one excludes a pair satisfying
the MUB symmetry budget. -/
theorem no_completion_pair_of_affinity_strict_lower_bound
    (p q : Fin 6 → Fin 3 → ℝ)
    (hp : 1 < modeAffinityTotal p)
    (hq : 1 < modeAffinityTotal q)
    (hbudget : modeAffinityTotal p + modeAffinityTotal q ≤ 2) : False := by
  exact no_affinity_pair_above_one
    (modeAffinityTotal p) (modeAffinityTotal q) hp hq hbudget

#print axioms one_le_modeAffinityTotal_of_row_collision
#print axioms modeMixingTotal_le_two_of_row_collision
#print axioms no_affinity_pair_above_one
#print axioms affinity_pair_eq_one_of_lower_bounds_and_budget
#print axioms completion_pair_forced_to_affinity_one
#print axioms no_completion_pair_of_affinity_strict_lower_bound

end D5.S3.Quantum.Tomography.MUBModeAffinitySharpBound
