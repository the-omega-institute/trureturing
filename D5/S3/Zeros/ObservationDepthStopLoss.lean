/- GID: D5/S3/Zeros/ObservationDepthStopLoss
   generality: G
   mirror-B: D5/B/S3/Zeros/ObservationDepthStopLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite stop-loss depth profiles obey sharp positivity and saturation bounds. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * The selected atom is residual-open with no coverage GID or formalization
     receipt. Its CAS text ends at `termwise calculation gives:` after defining
     the active height, tail count, remaining depth, and double-depth decay.
   * Repository searches for stop-loss, active-height, remaining-depth, and
     tail-count declarations found no semantic owner. Searches also checked
     natural truncated subtraction and positive-part spellings.
   * The following atom owns the integral, finite-difference, and derivative
     identities, so this module deliberately does not assert any of them.
   * Pinned Mathlib supplies `Finset.sum_nonneg`, `Finset.sum_le_sum`,
     `min_le_left`, `min_le_right`, and ordered-ring monotonicity of
     multiplication. They are applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.ObservationDepthStopLoss

open scoped BigOperators

/-- Height left by a pole at transverse distance `delta` after observation
depth `omega`. -/
def activePoleHeight (delta omega : ℝ) : ℝ :=
  max (delta - omega) 0

/-- Multiplicity of the poles still active at observation depth `omega`. -/
def horizontalTailCount {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega : ℝ) : ℕ :=
  ∑ j, if omega < delta j then multiplicity j else 0

/-- Total transverse depth remaining after observation depth `omega`. -/
def remainingDepth {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega : ℝ) : ℝ :=
  ∑ j, (multiplicity j : ℝ) * activePoleHeight (delta j) omega

/-- Total decay visible between two observation depths separated by `y`. -/
def doubleDepthDecay {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega y : ℝ) : ℝ :=
  ∑ j, (multiplicity j : ℝ) * min y (activePoleHeight (delta j) omega)

/-- A finite stop-loss profile has the source's initial values and sharp
pointwise-sum bounds. The last three implications exhibit equality at complete
cutoff, complete saturation, and in the linear regime. -/
theorem observation_depth_stop_loss
    {ι : Type*} [Fintype ι] (delta : ι → ℝ) (multiplicity : ι → ℕ)
    (deltaPositive : ∀ j, 0 < delta j) (omega y : ℝ) (yNonnegative : 0 ≤ y) :
    horizontalTailCount delta multiplicity 0 = ∑ j, multiplicity j ∧
      remainingDepth delta multiplicity 0 =
        ∑ j, (multiplicity j : ℝ) * delta j ∧
      doubleDepthDecay delta multiplicity omega 0 = 0 ∧
      0 ≤ remainingDepth delta multiplicity omega ∧
      0 ≤ doubleDepthDecay delta multiplicity omega y ∧
      doubleDepthDecay delta multiplicity omega y ≤
        remainingDepth delta multiplicity omega ∧
      doubleDepthDecay delta multiplicity omega y ≤
        y * ∑ j, (multiplicity j : ℝ) ∧
      ((∀ j, delta j ≤ omega) →
        remainingDepth delta multiplicity omega = 0 ∧
          doubleDepthDecay delta multiplicity omega y = 0) ∧
      ((∀ j, activePoleHeight (delta j) omega ≤ y) →
        doubleDepthDecay delta multiplicity omega y =
          remainingDepth delta multiplicity omega) ∧
      ((∀ j, y ≤ activePoleHeight (delta j) omega) →
        doubleDepthDecay delta multiplicity omega y =
          y * ∑ j, (multiplicity j : ℝ)) := by
  have heightNonnegative : ∀ j, 0 ≤ activePoleHeight (delta j) omega :=
    fun j => le_max_right _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [horizontalTailCount, deltaPositive]
  · apply Finset.sum_congr rfl
    intro j _
    simp [activePoleHeight, (deltaPositive j).le]
  · simp [doubleDepthDecay, activePoleHeight]
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (heightNonnegative j)
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (le_min yNonnegative (heightNonnegative j))
  · apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg _)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (min_le_left y (activePoleHeight (delta j) omega))
        (Nat.cast_nonneg (multiplicity j))
  · intro allCutOff
    have allHeightZero : ∀ j, activePoleHeight (delta j) omega = 0 :=
      fun j => by simp [activePoleHeight, sub_nonpos.mpr (allCutOff j)]
    constructor
    · simp [remainingDepth, allHeightZero]
    · simp [doubleDepthDecay, allHeightZero, min_eq_right yNonnegative]
  · intro allSaturated
    apply Finset.sum_congr rfl
    intro j _
    rw [min_eq_right (allSaturated j)]
  · intro allLinear
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [min_eq_left (allLinear j)]
    ring

/-- Without positive transverse distance, the initial tail count need not
equal total multiplicity. -/
theorem nonpositive_distance_breaks_initial_activity :
    horizontalTailCount (fun _ : Unit => (0 : ℝ)) (fun _ => 1) 0 ≠
      ∑ _ : Unit, (1 : ℕ) := by
  norm_num [horizontalTailCount]

/-- A negative depth increment makes the double-depth decay negative, so the
nonnegativity premise on `y` is necessary. -/
theorem negative_depth_breaks_decay_nonnegativity :
    doubleDepthDecay (fun _ : Unit => (1 : ℝ)) (fun _ => 1) 0 (-1) < 0 := by
  norm_num [doubleDepthDecay, activePoleHeight]

#print axioms observation_depth_stop_loss
#print axioms nonpositive_distance_breaks_initial_activity
#print axioms negative_depth_breaks_decay_nonnegativity

end D5.S3.Zeros.ObservationDepthStopLoss
