/- GID: D5/S3/Weil/Budget/ExplicitHyperbolicDegreeThreshold
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/ExplicitHyperbolicDegreeThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An explicit degree threshold makes a faster hyperbolic orbit dominate a bounded tail. -/

import Mathlib

/- Library-search audit trail (2026-09-01):
   * The atom ledger and formalization receipts contain no coverage for atom
     6fed6ad0a6feef01c8a213fef6cd1ac5d1996850370836f65d85b1714754af50.
     D5 searches for sinh, hyperbolic growth, growth rates, thresholds, and
     explicit degree bounds found no theorem giving this closed threshold.
     The neighboring `ChebyshevSlackPositivity` and `EvenChannelGhostNoGo`
     modules address different finite-orbit estimates.
   * Pinned Mathlib supplies `Real.sinh_eq`, exponential monotonicity,
     `Real.add_one_le_exp`, `Nat.lt_floor_add_one`, and
     `Real.exp_one_lt_three`; it has no packaged theorem with the comparison
     and explicit natural threshold below.
   * Searches across the pinned third-party Lean dependency closure found no
     matching hyperbolic-tail threshold theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.ExplicitHyperbolicDegreeThreshold

/-- For positive arguments, `sinh` lies between the elementary lower and
upper exponential estimates used in the orbit comparison. -/
theorem sinh_exp_two_sided {x : ℝ} (hx : 0 < x) :
    (Real.exp x - 1) / 2 ≤ Real.sinh x ∧
      Real.sinh x ≤ Real.exp x / 2 := by
  rw [Real.sinh_eq]
  have hNegExp : Real.exp (-x) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -x ≤ 0)
  have hNegExpPos : 0 < Real.exp (-x) := Real.exp_pos (-x)
  constructor <;> linarith

/-- Once `x` is at least one, the lower estimate can be written as a fixed
fraction of the leading exponential. -/
theorem exp_quarter_le_sinh {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x / 4 ≤ Real.sinh x := by
  have hExpTwo : 2 ≤ Real.exp x :=
    Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hx)
  have hLower := (sinh_exp_two_sided (lt_of_lt_of_le zero_lt_one hx)).1
  linarith

/-- A closed natural-number cutoff. The first term makes the target argument
at least one; the second leaves enough exponential gap to absorb `C`. -/
noncomputable def explicitDegreeThreshold
    (kappaZero kappaOne delta C : ℝ) : ℕ :=
  ⌊max (1 / kappaZero)
      (2 * C / (delta ^ 2 * (kappaZero - kappaOne)))⌋₊ + 1

/-- Beyond the explicit cutoff, the faster positive hyperbolic orbit strictly
dominates every tail with coefficient `C`. -/
theorem explicit_hyperbolic_degree_threshold
    (kappaZero kappaOne delta C : ℝ) (N : ℕ)
    (hkappaOne : 0 < kappaOne) (hRates : kappaOne < kappaZero)
    (hdelta : 0 < delta) (hC : 0 ≤ C)
    (hN : explicitDegreeThreshold kappaZero kappaOne delta C ≤ N) :
    C * Real.sinh ((N : ℝ) * kappaOne) ^ 2 <
      delta ^ 2 * Real.sinh ((N : ℝ) * kappaZero) ^ 2 := by
  have hkappaZero : 0 < kappaZero := hkappaOne.trans hRates
  have hGap : 0 < kappaZero - kappaOne := sub_pos.mpr hRates
  have hDeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hDenom : 0 < delta ^ 2 * (kappaZero - kappaOne) :=
    mul_pos hDeltaSq hGap
  let cutoff : ℝ := max (1 / kappaZero)
    (2 * C / (delta ^ 2 * (kappaZero - kappaOne)))
  have hCutoffLtFloor : cutoff < ((⌊cutoff⌋₊ + 1 : ℕ) : ℝ) := by
    simpa using Nat.lt_floor_add_one cutoff
  have hFloorLeN : (⌊cutoff⌋₊ + 1 : ℕ) ≤ N := by
    simpa only [explicitDegreeThreshold, cutoff] using hN
  have hFloorCastLeN : (((⌊cutoff⌋₊ + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast hFloorLeN
  have hCutoffLtN : cutoff < (N : ℝ) :=
    hCutoffLtFloor.trans_le hFloorCastLeN
  have hReciprocalLtN : 1 / kappaZero < (N : ℝ) :=
    (le_max_left _ _).trans_lt hCutoffLtN
  have hOneLtTarget : 1 < (N : ℝ) * kappaZero := by
    exact (div_lt_iff₀ hkappaZero).mp hReciprocalLtN
  have hRatioLtN :
      2 * C / (delta ^ 2 * (kappaZero - kappaOne)) < (N : ℝ) :=
    (le_max_right _ _).trans_lt hCutoffLtN
  have hLinearGap :
      4 * C < delta ^ 2 * (2 * (N : ℝ) * (kappaZero - kappaOne)) := by
    have hCleared := (div_lt_iff₀ hDenom).mp hRatioLtN
    nlinarith
  have hGapExponentLtExp :
      2 * (N : ℝ) * (kappaZero - kappaOne) <
        Real.exp (2 * (N : ℝ) * (kappaZero - kappaOne)) := by
    have hBasic := Real.add_one_le_exp
      (2 * (N : ℝ) * (kappaZero - kappaOne))
    linarith
  have hCoefficientGap :
      4 * C < delta ^ 2 *
        Real.exp (2 * (N : ℝ) * (kappaZero - kappaOne)) :=
    hLinearGap.trans
      (mul_lt_mul_of_pos_left hGapExponentLtExp hDeltaSq)
  have hExponentSplit :
      Real.exp (2 * (N : ℝ) * kappaZero) =
        Real.exp (2 * (N : ℝ) * (kappaZero - kappaOne)) *
          Real.exp (2 * (N : ℝ) * kappaOne) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hScaledGap :
      4 * C * Real.exp (2 * (N : ℝ) * kappaOne) <
        delta ^ 2 * Real.exp (2 * (N : ℝ) * kappaZero) := by
    have hMul := mul_lt_mul_of_pos_right hCoefficientGap
      (Real.exp_pos (2 * (N : ℝ) * kappaOne))
    rw [hExponentSplit]
    nlinarith
  have hTargetPositive : 0 < (N : ℝ) * kappaZero := by
    linarith
  have hTailPositive : 0 < (N : ℝ) * kappaOne := by
    have hNPositive : 0 < (N : ℝ) := by
      nlinarith [hkappaZero]
    exact mul_pos hNPositive hkappaOne
  have hTailUpper := (sinh_exp_two_sided hTailPositive).2
  have hTargetLower := exp_quarter_le_sinh hOneLtTarget.le
  have hTailSinhNonnegative : 0 ≤ Real.sinh ((N : ℝ) * kappaOne) :=
    (Real.sinh_nonneg_iff.mpr hTailPositive.le)
  have hTailExpHalfNonnegative :
      0 ≤ Real.exp ((N : ℝ) * kappaOne) / 2 := by positivity
  have hTargetExpQuarterNonnegative :
      0 ≤ Real.exp ((N : ℝ) * kappaZero) / 4 := by positivity
  have hTargetSinhNonnegative :
      0 ≤ Real.sinh ((N : ℝ) * kappaZero) :=
    (Real.sinh_nonneg_iff.mpr hTargetPositive.le)
  have hTailSq :
      Real.sinh ((N : ℝ) * kappaOne) ^ 2 ≤
        (Real.exp ((N : ℝ) * kappaOne) / 2) ^ 2 :=
    (sq_le_sq₀ hTailSinhNonnegative hTailExpHalfNonnegative).mpr hTailUpper
  have hTargetSq :
      (Real.exp ((N : ℝ) * kappaZero) / 4) ^ 2 ≤
        Real.sinh ((N : ℝ) * kappaZero) ^ 2 :=
    (sq_le_sq₀ hTargetExpQuarterNonnegative hTargetSinhNonnegative).mpr hTargetLower
  have hExpTailSq :
      Real.exp ((N : ℝ) * kappaOne) ^ 2 =
        Real.exp (2 * (N : ℝ) * kappaOne) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hExpTargetSq :
      Real.exp ((N : ℝ) * kappaZero) ^ 2 =
        Real.exp (2 * (N : ℝ) * kappaZero) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hExponentialComparison :
      C * (Real.exp ((N : ℝ) * kappaOne) / 2) ^ 2 <
        delta ^ 2 * (Real.exp ((N : ℝ) * kappaZero) / 4) ^ 2 := by
    rw [div_pow, div_pow]
    norm_num
    rw [hExpTailSq, hExpTargetSq]
    nlinarith
  exact (mul_le_mul_of_nonneg_left hTailSq hC).trans_lt
    (hExponentialComparison.trans_le
      (mul_le_mul_of_nonneg_left hTargetSq hDeltaSq.le))

/-- The requested numerical parameters give the concrete cutoff `401`. -/
theorem concrete_threshold_eq :
    explicitDegreeThreshold 1 (1 / 2) 1 100 = 401 := by
  norm_num [explicitDegreeThreshold]

/-- The closed cutoff theorem verifies the comparison at both its first
admissible degree and the following degree. -/
theorem concrete_threshold_checks :
    100 * Real.sinh ((401 : ℝ) * (1 / 2)) ^ 2 < Real.sinh 401 ^ 2 ∧
      100 * Real.sinh ((402 : ℝ) * (1 / 2)) ^ 2 < Real.sinh 402 ^ 2 := by
  constructor
  · simpa using explicit_hyperbolic_degree_threshold
      (kappaZero := 1) (kappaOne := 1 / 2) (delta := 1) (C := 100)
      (N := 401) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [explicitDegreeThreshold])
  · simpa using explicit_hyperbolic_degree_threshold
      (kappaZero := 1) (kappaOne := 1 / 2) (delta := 1) (C := 100)
      (N := 402) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [explicitDegreeThreshold])

/-- At degree one the same numerical comparison is false, so the threshold
is a substantive restriction rather than a vacuous decoration. -/
theorem concrete_degree_one_not_dominated :
    ¬100 * Real.sinh ((1 : ℝ) / 2) ^ 2 < Real.sinh 1 ^ 2 := by
  have hHalf : (1 / 2 : ℝ) ≤ Real.sinh (1 / 2) :=
    (Real.self_le_sinh_iff.mpr (by norm_num))
  have hHalfNonnegative : 0 ≤ Real.sinh (1 / 2) := by positivity
  have hHalfSq : (1 / 2 : ℝ) ^ 2 ≤ Real.sinh (1 / 2) ^ 2 :=
    (sq_le_sq₀ (by norm_num) hHalfNonnegative).mpr hHalf
  have hOneUpper := (sinh_exp_two_sided (by norm_num : (0 : ℝ) < 1)).2
  have hOne : Real.sinh 1 < (3 / 2 : ℝ) := by
    nlinarith [Real.exp_one_lt_three]
  have hOneNonnegative : 0 ≤ Real.sinh 1 := by positivity
  have hOneSq : Real.sinh 1 ^ 2 < (3 / 2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hOneNonnegative (by norm_num)).mpr hOne
  intro h
  nlinarith

#print axioms sinh_exp_two_sided
#print axioms exp_quarter_le_sinh
#print axioms explicit_hyperbolic_degree_threshold
#print axioms concrete_threshold_eq
#print axioms concrete_threshold_checks
#print axioms concrete_degree_one_not_dominated

end D5.S3.Weil.Budget.ExplicitHyperbolicDegreeThreshold
