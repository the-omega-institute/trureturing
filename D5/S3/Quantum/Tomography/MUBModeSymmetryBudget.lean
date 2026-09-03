/- GID: D5/S3/Quantum/Tomography/MUBModeSymmetryBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBModeSymmetryBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three-mode collision, mixing, and centered-affinity identities provide the scalar budget used by the strict-X MUB exclusion route. -/

import D5.S3.Quantum.Tomography.ZaunerCompletionFibre

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBModeSymmetryBudget

/-- Collision probability of one three-mode distribution. -/
def threeModeCollision (p : Fin 3 → ℝ) : ℝ :=
  (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2

/-- Linear entropy of one three-mode distribution. -/
def threeModeMixing (p : Fin 3 → ℝ) : ℝ :=
  1 - threeModeCollision p

/-- Squared displacement from the uniform three-mode distribution. -/
def threeModeCenteredSquare (p : Fin 3 → ℝ) : ℝ :=
  (p 0 - (1 / 3 : ℝ)) ^ 2 +
  (p 1 - (1 / 3 : ℝ)) ^ 2 +
  (p 2 - (1 / 3 : ℝ)) ^ 2

/-- On the probability simplex, three-mode mixing is twice the sum of the
three pair products. -/
theorem threeModeMixing_eq_pairProducts
    (p : Fin 3 → ℝ)
    (hsum : p 0 + p 1 + p 2 = 1) :
    threeModeMixing p =
      2 * (p 0 * p 1 + p 1 * p 2 + p 2 * p 0) := by
  unfold threeModeMixing threeModeCollision
  calc
    1 - ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2) =
        (p 0 + p 1 + p 2) ^ 2 -
          ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2) := by rw [hsum]; norm_num
    _ = 2 * (p 0 * p 1 + p 1 * p 2 + p 2 * p 0) := by ring

/-- Mixing is nonnegative for a nonnegative probability triple. -/
theorem threeModeMixing_nonneg
    (p : Fin 3 → ℝ)
    (hp : ∀ k, 0 ≤ p k)
    (hsum : p 0 + p 1 + p 2 = 1) :
    0 ≤ threeModeMixing p := by
  rw [threeModeMixing_eq_pairProducts p hsum]
  positivity

/-- The collision probability of a three-outcome distribution is at least
`1 / 3`. -/
theorem one_third_le_threeModeCollision
    (p : Fin 3 → ℝ)
    (hsum : p 0 + p 1 + p 2 = 1) :
    (1 / 3 : ℝ) ≤ threeModeCollision p := by
  have hsq :
      0 ≤ (p 0 - p 1) ^ 2 +
        (p 1 - p 2) ^ 2 +
        (p 2 - p 0) ^ 2 := by positivity
  unfold threeModeCollision
  nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) hsum]

/-- Three-mode mixing is at most `2 / 3`. -/
theorem threeModeMixing_le_two_thirds
    (p : Fin 3 → ℝ)
    (hsum : p 0 + p 1 + p 2 = 1) :
    threeModeMixing p ≤ (2 / 3 : ℝ) := by
  unfold threeModeMixing
  linarith [one_third_le_threeModeCollision p hsum]

/-- The centered-square and collision coordinates differ by the uniform
baseline `1 / 3`. -/
theorem threeModeCenteredSquare_eq_collision_sub_one_third
    (p : Fin 3 → ℝ)
    (hsum : p 0 + p 1 + p 2 = 1) :
    threeModeCenteredSquare p =
      threeModeCollision p - (1 / 3 : ℝ) := by
  unfold threeModeCenteredSquare threeModeCollision
  nlinarith

/-- Maximal three-mode mixing occurs exactly at the uniform distribution. -/
theorem threeModeMixing_eq_two_thirds_iff
    (p : Fin 3 → ℝ)
    (hsum : p 0 + p 1 + p 2 = 1) :
    threeModeMixing p = (2 / 3 : ℝ) ↔
      p 0 = (1 / 3 : ℝ) ∧
      p 1 = (1 / 3 : ℝ) ∧
      p 2 = (1 / 3 : ℝ) := by
  constructor
  · intro hmix
    have hcollision : threeModeCollision p = (1 / 3 : ℝ) := by
      unfold threeModeMixing at hmix
      linarith
    have hcenter :=
      threeModeCenteredSquare_eq_collision_sub_one_third p hsum
    rw [hcollision] at hcenter
    have hzero : threeModeCenteredSquare p = 0 := by
      simpa using hcenter
    unfold threeModeCenteredSquare at hzero
    have h0 : p 0 = (1 / 3 : ℝ) := by
      nlinarith [sq_nonneg (p 0 - (1 / 3 : ℝ)),
        sq_nonneg (p 1 - (1 / 3 : ℝ)),
        sq_nonneg (p 2 - (1 / 3 : ℝ))]
    have h1 : p 1 = (1 / 3 : ℝ) := by
      nlinarith [sq_nonneg (p 0 - (1 / 3 : ℝ)),
        sq_nonneg (p 1 - (1 / 3 : ℝ)),
        sq_nonneg (p 2 - (1 / 3 : ℝ))]
    have h2 : p 2 = (1 / 3 : ℝ) := by
      nlinarith [sq_nonneg (p 0 - (1 / 3 : ℝ)),
        sq_nonneg (p 1 - (1 / 3 : ℝ)),
        sq_nonneg (p 2 - (1 / 3 : ℝ))]
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    simp [threeModeMixing, threeModeCollision, h0, h1, h2]
    norm_num

/-- Total collision of six three-mode probability rows. -/
def modeCollisionTotal (p : Fin 6 → Fin 3 → ℝ) : ℝ :=
  ∑ i, threeModeCollision (p i)

/-- Total mode mixing of six probability rows. -/
def modeMixingTotal (p : Fin 6 → Fin 3 → ℝ) : ℝ :=
  ∑ i, threeModeMixing (p i)

/-- Total squared displacement from uniform mode weights. -/
def modeCenteredSquareTotal (p : Fin 6 → Fin 3 → ℝ) : ℝ :=
  ∑ i, threeModeCenteredSquare (p i)

/-- The normalized symmetry-plane affinity coordinate. This algebraic
coordinate becomes the chordal subspace affinity after the projector-plane
bridge is supplied. -/
def modeAffinityTotal (p : Fin 6 → Fin 3 → ℝ) : ℝ :=
  (modeCollisionTotal p - 2) / 2

/-- Total mixing equals six minus total collision. -/
theorem modeMixingTotal_eq_six_sub_collision
    (p : Fin 6 → Fin 3 → ℝ) :
    modeMixingTotal p = 6 - modeCollisionTotal p := by
  simp [modeMixingTotal, modeCollisionTotal, threeModeMixing]

/-- The total centered square is the collision excess above the six-row
uniform baseline. -/
theorem modeCenteredSquareTotal_eq_collision_sub_two
    (p : Fin 6 → Fin 3 → ℝ)
    (hsum : ∀ i, p i 0 + p i 1 + p i 2 = 1) :
    modeCenteredSquareTotal p = modeCollisionTotal p - 2 := by
  unfold modeCenteredSquareTotal modeCollisionTotal
  calc
    ∑ i, threeModeCenteredSquare (p i) =
        ∑ i, (threeModeCollision (p i) - (1 / 3 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact threeModeCenteredSquare_eq_collision_sub_one_third
            (p i) (hsum i)
    _ = (∑ i, threeModeCollision (p i)) - 2 := by
      rw [Finset.sum_sub_distrib]
      norm_num

/-- Affinity is one half of the total centered-square displacement. -/
theorem modeAffinityTotal_eq_half_centeredSquare
    (p : Fin 6 → Fin 3 → ℝ)
    (hsum : ∀ i, p i 0 + p i 1 + p i 2 = 1) :
    modeAffinityTotal p = modeCenteredSquareTotal p / 2 := by
  rw [modeCenteredSquareTotal_eq_collision_sub_two p hsum]
  rfl

/-- Mixing and affinity are complementary coordinates: `M = 4 - 2 alpha`. -/
theorem modeMixingTotal_eq_four_sub_two_mul_affinity
    (p : Fin 6 → Fin 3 → ℝ) :
    modeMixingTotal p = 4 - 2 * modeAffinityTotal p := by
  rw [modeMixingTotal_eq_six_sub_collision]
  unfold modeAffinityTotal
  ring

/-- Six normalized probability rows have total mode mixing between zero and
four. -/
theorem modeMixingTotal_mem_Icc
    (p : Fin 6 → Fin 3 → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    (hsum : ∀ i, p i 0 + p i 1 + p i 2 = 1) :
    modeMixingTotal p ∈ Set.Icc (0 : ℝ) 4 := by
  constructor
  · unfold modeMixingTotal
    exact Finset.sum_nonneg fun i hi ↦
      threeModeMixing_nonneg (p i) (hp i) (hsum i)
  · unfold modeMixingTotal
    calc
      ∑ i, threeModeMixing (p i) ≤ ∑ _i : Fin 6, (2 / 3 : ℝ) :=
        Finset.sum_le_sum fun i hi ↦
          threeModeMixing_le_two_thirds (p i) (hsum i)
      _ = 4 := by norm_num

#print axioms threeModeMixing_eq_pairProducts
#print axioms threeModeMixing_nonneg
#print axioms one_third_le_threeModeCollision
#print axioms threeModeMixing_le_two_thirds
#print axioms threeModeCenteredSquare_eq_collision_sub_one_third
#print axioms threeModeMixing_eq_two_thirds_iff
#print axioms modeMixingTotal_eq_six_sub_collision
#print axioms modeCenteredSquareTotal_eq_collision_sub_two
#print axioms modeAffinityTotal_eq_half_centeredSquare
#print axioms modeMixingTotal_eq_four_sub_two_mul_affinity
#print axioms modeMixingTotal_mem_Icc

end D5.S3.Quantum.Tomography.MUBModeSymmetryBudget
